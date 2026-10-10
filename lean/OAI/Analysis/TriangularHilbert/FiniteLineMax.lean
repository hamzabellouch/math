import OAI.Analysis.TriangularHilbert.GaussianRadial

namespace OAI

universe uκ

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

def lineExtend (D : Finset ℤ) (f : D → ℝ) (n : ℤ) : ℝ :=
  if hn : n ∈ D then f ⟨n,hn⟩ else 0

lemma lineExtend_apply (D : Finset ℤ) (f : D → ℝ) (n : D) : lineExtend D f n = f n := by
  simp only [lineExtend,dite_eq_left n.property]

lemma sum_lineExtend (D : Finset ℤ) (f : D → ℝ) (g : ℤ → ℝ) :
    (∑ n ∈ D, lineExtend D f n*g n) = ∑ n : D, f n*g n := by
  rw [← Finset.sum_coe_sort]
  simp only [lineExtend_apply]

def lineMax (D : Finset ℤ) (f : D → ℝ) (n : ℤ) : ℝ := intMax D (lineExtend D f) n

lemma lineMax_nonneg (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m) (n : ℤ) :
    0 ≤ lineMax D f n := by
  exact intMax_nonneg D (lineExtend D f) (fun m hm => by simpa only [lineExtend,dite_eq_left hm] using hf ⟨m,hm⟩) n

lemma lineMax_strong (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m)
    {κ : Type uκ} [Fintype κ] (u : κ → ℤ) (hu : Function.Injective u) :
    (∑ n, lineMax D f (u n)*Real.sqrt (lineMax D f (u n))) ≤
      18*Real.sqrt 2 * ∑ m : D, f m*Real.sqrt (f m) := by
  classical
  have hi := intMax_strong D (Finset.univ.image u) (lineExtend D f)
    (fun m hm => by simpa only [lineExtend,dite_eq_left hm] using hf ⟨m,hm⟩)
  rw [Finset.sum_image (fun _ _ _ _ h => hu h)] at hi
  rw [← Finset.sum_coe_sort D (fun m => lineExtend D f m*Real.sqrt (lineExtend D f m))] at hi
  simpa only [lineMax,lineExtend_apply] using hi

lemma gaussian_sum_le_lineMax (D : Finset ℤ) (f : D → ℝ) (hf : ∀ m, 0 ≤ f m)
    {σ h : ℝ} (hh : 0 < h) (hσ : h^2 ≤ σ) (n : ℤ) :
    (∑ m : D, f m*(h*Heat.density σ (h*((m-n:ℤ):ℝ)))) ≤ Heat.meshMassConstant*lineMax D f n := by
  have hi := Heat.gaussian_sum_le_intMax D (lineExtend D f)
    (fun m hm => by simpa only [lineExtend,dite_eq_left hm] using hf ⟨m,hm⟩) hh hσ n
  rw [sum_lineExtend] at hi
  exact hi

lemma cubic_young {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a*b ≤ (a^3+2*b*Real.sqrt b)/3 := by
  have hs := Real.sq_sqrt hb
  have hnn : 0 ≤ (a-Real.sqrt b)^2*(a+2*Real.sqrt b) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  have hs3 : (Real.sqrt b)^3 = b*Real.sqrt b := by rw [pow_succ,hs]
  have ha2 : a*(Real.sqrt b)^2 = a*b := by rw [hs]
  nlinarith only [hnn,hs3,ha2]

lemma sum_abs_sq_sqrt {κ : Type uκ} [Fintype κ] (f : κ → ℂ) :
    (∑ m, ‖f m‖^2*Real.sqrt (‖f m‖^2)) = ∑ m, ‖f m‖^3 := by
  apply Finset.sum_congr rfl
  intro m _
  rw [Real.sqrt_sq (norm_nonneg _)]; ring

lemma lineMax_scalar_product_bound (D : Finset ℤ) (f : D → ℂ)
    {κ : Type uκ} [Fintype κ] (u : κ → ℤ) (hu : Function.Injective u) (a : κ → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i*lineMax D (fun m => ‖f m‖^2) (u i)) ≤
      ((∑ i, a i^3)+36*Real.sqrt 2*(∑ m, ‖f m‖^3))/3 := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset κ)) =>
    cubic_young (ha i) (lineMax_nonneg D (fun m => ‖f m‖^2) (fun m => sq_nonneg _) (u i)))
  have hm := lineMax_strong D (fun m => ‖f m‖^2) (fun m => sq_nonneg _) u hu
  rw [sum_abs_sq_sqrt] at hm
  simp only [mul_assoc,← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum] at hs
  linarith
end
end TriangularHilbert
end

end OAI
