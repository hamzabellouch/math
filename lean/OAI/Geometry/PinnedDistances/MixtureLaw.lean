import OAI.Geometry.PinnedDistances.EnergyLaw

namespace OAI

universe u1 u2 u3

section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace WeakPinned.Bounded

variable {I : Type u1} {V : Type u2} {X : Type u3} [Fintype I] [Fintype V]

def edgeWeight (w : I → ℝ) (p : I → V → ℝ) (r : I × V) : ℝ := w r.1*p r.1 r.2

def tripleWeight (w : I → ℝ) (p : I → V → ℝ) (r : I × V × V × V) : ℝ :=
  w r.1*p r.1 r.2.1*p r.1 r.2.2.1*p r.1 r.2.2.2

lemma sum_edgeWeight (w : I → ℝ) (p : I → V → ℝ)
    (hw : ∑ i,w i=1) (hp : ∀ i,∑ x,p i x=1) : ∑ r,edgeWeight w p r=1 := by
  simp only [edgeWeight,Fintype.sum_prod_type,← Finset.mul_sum,hp,mul_one,hw]

lemma sum_tripleWeight (w : I → ℝ) (p : I → V → ℝ)
    (hw : ∑ i,w i=1) (hp : ∀ i,∑ x,p i x=1) : ∑ r,tripleWeight w p r=1 := by
  simp only [tripleWeight,Fintype.sum_prod_type,← Finset.mul_sum,hp,mul_one,hw]

def edgeValue (s : I → V) (U₁ U₂ : V → X) (r : I × V) : Quad X :=
  (U₁ (s r.1),U₂ (s r.1),U₁ r.2,U₂ r.2)

def tripleValue (s : I → V) (U₁ U₂ : V → X) (r : I × V × V × V) : Expanded X :=
  (edgeValue s U₁ U₂ (r.1,r.2.1),((U₁ r.2.2.1,U₂ r.2.2.1),(U₁ r.2.2.2,U₂ r.2.2.2)))

lemma triple_integral (w : I → ℝ) (p : I → V → ℝ) (F : I → V → ℝ) (g h : V → ℝ) :
    (∑ r,tripleWeight w p r*(F r.1 r.2.1*g r.2.2.1*h r.2.2.2))=
      ∑ i,w i*(∑ y,p i y*F i y)*(∑ z,p i z*g z)*(∑ z,p i z*h z) := by
  simp only [tripleWeight,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ y,∑ z,∑ t,(w i*p i y*F i y)*(p i z*g z)*(p i t*h t) := by
      apply Finset.sum_congr rfl; intro y _
      apply Finset.sum_congr rfl; intro z _
      apply Finset.sum_congr rfl; intro t _
      ring
    _ = (∑ y,w i*(p i y*F i y))*(∑ z,p i z*g z)*(∑ t,p i t*h t) := by
      simp only [← Finset.mul_sum,← Finset.sum_mul]
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      ring
    _ = _ := by rw [← Finset.mul_sum]

lemma avg_abs_bound (p : V → ℝ) (f : V → ℝ) (H : ℝ)
    (hp : ∀ x,0≤p x) (hpsum : ∑ x,p x=1) (hf : ∀ x,|f x|≤H) :
    |∑ x,p x*f x|≤H := by
  calc
    _ ≤ ∑ x,|p x*f x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x,p x*|f x| := by simp only [abs_mul,abs_of_nonneg (hp _)]
    _ ≤ ∑ x,p x*H := Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hf x) (hp x))
    _ = H := by rw [← Finset.sum_mul,hpsum,one_mul]

lemma pair_test_error (m₁ m₂ A₁ A₂ H₁ H₂ : ℝ) (hm₂ : |m₂|≤H₂) (hA₁ : |A₁|≤H₁) :
    |m₁*m₂-A₁*A₂|≤H₂*|m₁-A₁|+H₁*|m₂-A₂| := by
  calc
    _ = |(m₁-A₁)*m₂+A₁*(m₂-A₂)| := by congr 1; ring
    _ ≤ |(m₁-A₁)*m₂|+|A₁*(m₂-A₂)| := abs_add_le _ _
    _ ≤ _ := by rw [abs_mul,abs_mul]; nlinarith [abs_nonneg (m₁-A₁),abs_nonneg (m₂-A₂)]

lemma mixture_pair_test_bound (w : I → ℝ) (p : I → V → ℝ) (F : I → V → ℝ)
    (g h : V → ℝ) (A₁ A₂ C H₁ H₂ : ℝ)
    (hw : ∀ i,0≤w i) (hp : ∀ i x,0≤p i x) (hpsum : ∀ i,∑ x,p i x=1)
    (hC : 0≤C) (hF : ∀ i x,|F i x|≤C) (hh : ∀ x,|h x|≤H₂)
    (hA₁ : |A₁|≤H₁) :
    |(∑ r,tripleWeight w p r*(F r.1 r.2.1*g r.2.2.1*h r.2.2.2))-
      (∑ r,edgeWeight w p r*F r.1 r.2)*A₁*A₂|≤
      C*(H₂*(∑ i,w i*|(∑ z,p i z*g z)-A₁|)+H₁*(∑ i,w i*|(∑ z,p i z*h z)-A₂|)) := by
  let M := fun i => ∑ y,p i y*F i y
  let G := fun i => ∑ z,p i z*g z
  let H := fun i => ∑ z,p i z*h z
  have hMC (i) : |M i|≤C := avg_abs_bound _ _ _ (hp i) (hpsum i) (hF i)
  rw [triple_integral]
  have he : (∑ r,edgeWeight w p r*F r.1 r.2)=∑ i,w i*M i := by
    simp only [edgeWeight,Fintype.sum_prod_type,M,Finset.mul_sum,mul_assoc]
  rw [he]
  change |(∑ i,w i*M i*G i*H i)-(∑ i,w i*M i)*A₁*A₂|≤_
  simp only [Finset.sum_mul,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i,|w i*M i*G i*H i-w i*M i*A₁*A₂| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i,w i*|M i| *|G i*H i-A₁*A₂| := by
      apply Finset.sum_congr rfl; intro i _
      rw [show w i*M i*G i*H i-w i*M i*A₁*A₂ = w i*M i*(G i*H i-A₁*A₂) by ring]
      rw [abs_mul,abs_mul,abs_of_nonneg (hw i)]
    _ ≤ ∑ i,w i*C*(H₂*|G i-A₁|+H₁*|H i-A₂|) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hMC i) (hw i)
      · exact pair_test_error _ _ _ _ _ _ (avg_abs_bound _ _ _ (hp i) (hpsum i) hh) hA₁
      · exact abs_nonneg _
      · exact mul_nonneg (hw i) hC
    _ = _ := by simp only [Finset.mul_sum,← Finset.sum_add_distrib,G,H]; apply Finset.sum_congr rfl; intros; ring

end WeakPinned.Bounded

end
end
section
end

end OAI
