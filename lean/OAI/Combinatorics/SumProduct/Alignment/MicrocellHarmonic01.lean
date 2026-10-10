import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.HarmonicExposure02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
end
end

section
noncomputable section
namespace RoughFaceShift
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open scoped BigOperators Topology
variable {G : Type} [Group G] [TopologicalSpace G] {dim : ℕ}
variable (Γ : Subgroup G) [MetricSpace (G⧸Γ)]
variable [IsTopologicalGroup G] (c : RealCoordinates G dim)

 
theorem raw_conditional_face_uniform (hsk : SecondKind c)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (htop : (inferInstance : MetricSpace (G⧸Γ)).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace Γ)
    (m v D d : ℕ) (hd : 0<d) (c₀ C₀ : ℝ) (B K : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w M : ℕ→ℕ) (U V : ℕ → Fin m → ℝ) (Z0 H : ℕ→ℝ) (L : ℕ→ℤ)
    (hw : Tendsto w atTop atTop) (hU : ∀ j,Tendsto (fun n=>U n j) atTop atTop)
    (hUV : ∀ n j,U n j≤V n j)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z0 n/(1+∑ j,V n j)^a) atTop atTop)
    (hH : ∀ n,0≤H n) (hHZ : Tendsto (fun n=>H n/Z0 n) atTop (𝓝 0))
    (hM : ∀ n,0<M n) (hMs : ∀ n,Smooth (w n) (M n:ℤ))
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n)
    (hUL : ∀ j,Tendsto (fun n=>U n j/(L n:ℝ)) atTop atTop) :
    ∀ ε : ℝ,0<ε →∀ᶠ n in atTop,
      ∀ b : Exposure m,b.Legal (U n) (V n) (Z0 n) (w n) (M n) →
      ∀ X W : ℕ,(W:ℤ)∣(M n:ℤ) → b.a.natAbs.Coprime W →
      (∀ t∈productTimes b.S b.r (L n),(X:ℝ)≤b.Q/(∏ j,(t j:ℝ))) →
      (∀ t∈productTimes b.S b.r (L n),(b.Q+b.Δ)/(∏ j,(t j:ℝ))≤(X:ℝ)^2) →
      ∀ (A : Fin v → ℤ) (P : (Fin (m+v)→ℝ)→G),
      (∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ∀ (σ : (G⧸Γ) → (G⧸Γ)),LipschitzWith K σ →
      ∀ h : (Fin m → ℤ) → Fin v → ℤ,
      (∀ t∈productTimes b.S b.r (L n),∀ i,(d:ℤ)∣h t i ∧ |(h t i:ℝ)|≤H n) →
      (∀ t∈productTimes b.S b.r (L n),∀ x : Fin v → ℤ,
        σ (QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>(x i:ℝ)))))=
          QuotientGroup.mk (P (Fin.append (fun j=>(t j:ℝ)) (fun i=>((x i+h t i:ℤ):ℝ))))) →
      HarmonicExposure.rawFiberMass
        (exceptionalFace Γ m v c₀ C₀ B η b.Z d (M n) A P σ b.S b.r (L n))
        X W b.Q b.Δ b.a (M n) /
      HarmonicExposure.rawFiberMass (productTimes b.S b.r (L n))
        X W b.Q b.Δ b.a (M n)<ε
 := by
  classical
  intro ε hε
  have hu := conditional_face_uniform (Γ:=Γ) (c:=c) hsk hΓ htop m v D d hd
    c₀ C₀ B K η hc₀ hC₀ hB hη w M U V Z0 H L hw hU hUV hZ hH hHZ
    hM hMs hL hsm hWL hUL ε hε
  have hup : ∀ᶠ n in atTop,∀ j,0<U n j :=
    eventually_all.mpr (fun j=>(hU j).eventually (eventually_gt_atTop 0))
  filter_upwards [hu,hup] with n hn hUn
  intro b hb X W hWM ha hlo hhi A P hP σ hσ h hh hid
  have hτ : ∀ t∈productTimes b.S b.r (L n),0<∏ j,(t j:ℝ) := by
    intro t ht
    apply Finset.prod_pos
    intro j hj
    have htj := Fintype.mem_piFinset.mp ht j
    have htpos := (mem_times (b.S j) (b.r j) (L n) (t j) (hL n)).mp htj
    exact (hUn j).trans_le (((hb.1 j).1).trans htpos.1)
  have he (T : Finset (Fin m→ℤ)) (hT : T⊆productTimes b.S b.r (L n)) :=
    HarmonicExposure.rawFiberMass_eq_exposed T X W b.Q b.Δ b.a (M n)
      (by exact_mod_cast hM n) hWM ha
      (fun t ht=>hτ t (hT ht)) (fun t ht=>hlo t (hT ht)) (fun t ht=>hhi t (hT ht))
  have hsub : exceptionalFace Γ m v c₀ C₀ B η b.Z d (M n) A P σ b.S b.r (L n) ⊆
      productTimes b.S b.r (L n) := Finset.filter_subset _ _
  rw [he _ hsub,he _ (Finset.Subset.refl _)]
  exact hn b hb A P hP σ hσ h hh hid

end RoughFaceShift
end
end

section
noncomputable section
namespace HarmonicExposure
open RoughSamplingWeights RoughSourceExceptional RoughProductRemoval Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def rawTailFiber {m : ℕ} (X : Fin m→ℕ) (W : ℕ) (S : Fin m→ℝ)
    (r : Fin m→ℤ) (L : ℤ) : Finset (Fin m→ℕ) := by
  classical
  exact Fintype.piFinset (fun j=>(Ico (X j) ((X j)^2)).filter (fun t=>
    W.Coprime t ∧ S j≤(t:ℝ) ∧ (t:ℝ)<2*S j ∧ L∣(t:ℤ)-r j))

def literalFiberMass {m : ℕ} (E : Set (Fin m→ℤ)) (X : Fin m→ℕ) (Xp W : ℕ)
    (S : Fin m→ℝ) (r : Fin m→ℤ) (L : ℤ) (Q Δ : ℝ) (a M : ℤ) : ℝ := by
  classical
  exact ∑ t∈(rawTailFiber X W S r L).filter (fun t=>(fun j=>(t j:ℤ))∈E),
    (∏ j,(t j:ℝ)⁻¹)*∑ p∈pivotFiber Xp Q Δ (∏ j,(t j:ℝ)) a M,
      if W.Coprime p then (p:ℝ)⁻¹ else 0

lemma rawTail_cast_mem {m : ℕ} (X : Fin m→ℕ) (W : ℕ) (S : Fin m→ℝ)
    (r : Fin m→ℤ) (L : ℤ) (hL : 0<L) (t : Fin m→ℕ)
    (ht : t∈rawTailFiber X W S r L) : (fun j=>(t j:ℤ))∈productTimes S r L := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro j
  have hj := mem_filter.mp (Fintype.mem_piFinset.mp ht j)
  apply (mem_times (S j) (r j) L (t j) hL).mpr
  obtain ⟨z,hz⟩ := hj.2.2.2.2
  exact ⟨by simpa using hj.2.2.1,by simpa using hj.2.2.2.1,z,by linarith⟩

lemma times_nonneg {m : ℕ} (X : Fin m→ℕ) (S : Fin m→ℝ) (r : Fin m→ℤ) (L : ℤ)
    (hL : 0<L) (hlo : ∀ j,(X j:ℝ)≤S j) (t : Fin m→ℤ)
    (ht : t∈productTimes S r L) (j : Fin m) : 0≤t j := by
  have hj := (mem_times (S j) (r j) L (t j) hL).mp (Fintype.mem_piFinset.mp ht j)
  have hn : (0:ℝ)≤(t j:ℝ) := (Nat.cast_nonneg (X j)).trans ((hlo j).trans hj.1)
  exact_mod_cast hn

lemma times_nat_mem {m : ℕ} (X : Fin m→ℕ) (W : ℕ) (S : Fin m→ℝ)
    (r : Fin m→ℤ) (L : ℤ) (hL : 0<L) (hWL : (W:ℤ)∣L)
    (hr : ∀ j,(r j).natAbs.Coprime W)
    (hlo : ∀ j,(X j:ℝ)≤S j) (hhi : ∀ j,2*S j≤(X j:ℝ)^2)
    (t : Fin m→ℤ) (ht : t∈productTimes S r L) :
    (fun j=>(t j).toNat)∈rawTailFiber X W S r L := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro j
  have hj := (mem_times (S j) (r j) L (t j) hL).mp (Fintype.mem_piFinset.mp ht j)
  have hn : ((t j).toNat:ℤ)=t j := Int.toNat_of_nonneg (times_nonneg X S r L hL hlo t ht j)
  have hnr : ((t j).toNat:ℝ)=(t j:ℝ) := by exact_mod_cast hn
  obtain ⟨z,hz⟩ := hj.2.2
  have hcong : L∣((t j).toNat:ℤ)-r j := ⟨z,by rw [hn,hz]; ring⟩
  apply mem_filter.mpr
  refine ⟨mem_Ico.mpr ⟨?_,?_⟩,residue_unit W (t j).toNat (r j) L hWL (hr j) hcong,
    ?_,?_,hcong⟩
  · have hh := (hlo j).trans hj.1
    rw [←hnr] at hh
    exact_mod_cast hh
  · have hh := hj.2.1.trans_le (hhi j)
    rw [←hnr] at hh
    exact_mod_cast hh
  · rw [hnr]
    exact hj.1
  · rw [hnr]
    exact hj.2.1

 

theorem literal_mass_eq {m : ℕ} (E : Set (Fin m→ℤ)) (X : Fin m→ℕ) (Xp W : ℕ)
    (S : Fin m→ℝ) (r : Fin m→ℤ) (L : ℤ) (Q Δ : ℝ) (a M : ℤ)
    (hL : 0<L) (hWL : (W:ℤ)∣L) (hr : ∀ j,(r j).natAbs.Coprime W)
    (hlo : ∀ j,(X j:ℝ)≤S j) (hhi : ∀ j,2*S j≤(X j:ℝ)^2) :
    literalFiberMass E X Xp W S r L Q Δ a M =
      rawFiberMass ((productTimes S r L).filter (fun t=>t∈E)) Xp W Q Δ a M
 := by
  classical
  unfold literalFiberMass rawFiberMass
  apply sum_bij (fun t _=>fun j=>(t j:ℤ))
  · intro t ht
    obtain ⟨ht,hE⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨rawTail_cast_mem X W S r L hL t ht,hE⟩
  · intro t ht u hu he
    funext j
    exact_mod_cast congrFun he j
  · intro t ht
    obtain ⟨ht,hE⟩ := mem_filter.mp ht
    have hh : (fun j=>((t j).toNat:ℤ))=t := funext (fun j=>
      Int.toNat_of_nonneg (times_nonneg X S r L hL hlo t ht j))
    refine ⟨fun j=>(t j).toNat,mem_filter.mpr ⟨times_nat_mem X W S r L hL hWL hr hlo hhi t ht,?_⟩,hh⟩
    rwa [hh]
  · intro t ht
    simp only [Int.cast_natCast]

end HarmonicExposure
end
end

section

 

 

section RawSuccessInlineScope0
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
namespace MicrocellHarmonic
variable {I : Type*} [Fintype I] [Nonempty I]

 
def weight (w : I → ℝ) (i : I) : ℝ := w i / ∑ j,w j

def uniform (_i : I) : ℝ := (Fintype.card I : ℝ)⁻¹

lemma total_pos (w : I → ℝ) (hw : ∀ i,0<w i) : 0 < ∑ i,w i :=
  Finset.sum_pos (fun i _=>hw i) Finset.univ_nonempty

lemma sum_weight (w : I → ℝ) (hw : ∀ i,0<w i) : ∑ i,weight w i=1 := by
  simp only [weight,←Finset.sum_div]
  exact div_self (total_pos w hw).ne'

 

theorem normalized_error (w : I → ℝ) (hw : ∀ i,0<w i) (ε : ℝ)
    (he : ∀ i j, |w i-w j| ≤ ε*w j) (i : I) :
    |weight w i-uniform i| ≤ ε/(Fintype.card I : ℝ) := by
  have hc : (0:ℝ)<Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hW := total_pos w hw
  have hn : |∑ j,(w i-w j)| ≤ ε*∑ j,w j := by
    calc
      _ ≤ ∑ j,|w i-w j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j,ε*w j := Finset.sum_le_sum (fun j _=>he i j)
      _ = _ := by rw [Finset.mul_sum]
  have heq : weight w i-uniform i = (∑ j,(w i-w j))/((Fintype.card I : ℝ)*(∑ j,w j)) := by
    simp only [weight,uniform,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
  rw [heq,abs_div,abs_of_pos (mul_pos hc hW)]
  calc
    _ ≤ (ε*∑ j,w j)/((Fintype.card I : ℝ)*(∑ j,w j)) :=
      div_le_div_of_nonneg_right hn (mul_pos hc hW).le
    _ = _ := by field_simp

 

theorem l1_error (w : I → ℝ) (hw : ∀ i,0<w i) (ε : ℝ)
    (he : ∀ i j, |w i-w j| ≤ ε*w j) :
    (∑ i,|weight w i-uniform i|) ≤ ε := by
  have hc : (Fintype.card I : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ∑ i,ε/(Fintype.card I : ℝ) := Finset.sum_le_sum (fun i _=>normalized_error w hw ε he i)
    _ = ε := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; field_simp

 

theorem test_error (w : I → ℝ) (hw : ∀ i,0<w i) (ε B : ℝ)
    (hB : 0 ≤ B) (he : ∀ i j, |w i-w j| ≤ ε*w j)
    (f : I → ℝ) (hf : ∀ i,|f i|≤B) :
    |(∑ i,weight w i*f i)-(∑ i,uniform i*f i)| ≤ B*ε := by
  rw [←Finset.sum_sub_distrib]
  calc
    _ = |∑ i,(weight w i-uniform i)*f i| := by congr 1; apply Finset.sum_congr rfl; intro i _; ring
    _ ≤ ∑ i,|(weight w i-uniform i)*f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,B*|weight w i-uniform i| := Finset.sum_le_sum (by
      intro i _; rw [abs_mul,mul_comm B]; exact mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _))
    _ = B*∑ i,|weight w i-uniform i| := (Finset.mul_sum _ _ _).symm
    _ ≤ B*ε := mul_le_mul_of_nonneg_left (l1_error w hw ε he) hB

lemma reciprocal_oscillation {X R x y : ℝ} (hX : 0<X) (hR : 0≤R)
    (hx : X≤x) (hx' : x≤X+R) (hy : X≤y) (hy' : y≤X+R) :
    |x⁻¹-y⁻¹| ≤ (R/X)*y⁻¹ := by
  have hx0 : 0<x := hX.trans_le hx
  have hy0 : 0<y := hX.trans_le hy
  have heq : x⁻¹-y⁻¹=(y-x)/(x*y) := by field_simp
  have hdiff : |y-x|≤R := (abs_le.mpr ⟨by linarith,by linarith⟩)
  rw [heq,abs_div,abs_of_pos (mul_pos hx0 hy0)]
  calc
    _ ≤ R/(x*y) := div_le_div_of_nonneg_right hdiff (mul_pos hx0 hy0).le
    _ ≤ R/(X*y) := div_le_div_of_nonneg_left hR (mul_pos hX hy0) (mul_le_mul_of_nonneg_right hx hy0.le)
    _ = _ := by ring

 

theorem harmonic_test_error (p : I → ℝ) (X R : ℝ) (hX : 0<X) (hR : 0≤R)
    (hp : ∀ i,X≤p i ∧ p i≤X+R) (f : I → ℝ) (hf : ∀ i,|f i|≤1) :
    |(∑ i,weight (fun j=>(p j)⁻¹) i*f i)-(∑ i,uniform i*f i)| ≤ R/X := by
  simpa only [one_mul] using test_error (fun j=>(p j)⁻¹)
    (fun j=>inv_pos.mpr (hX.trans_le (hp j).1)) (R/X) 1 zero_le_one
    (fun i j=>reciprocal_oscillation hX hR (hp i).1 (hp i).2 (hp j).1 (hp j).2) f hf

end MicrocellHarmonic

end
end RawSuccessInlineScope0
end

end OAI
