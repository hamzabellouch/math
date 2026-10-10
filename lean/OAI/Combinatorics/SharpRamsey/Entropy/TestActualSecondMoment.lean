import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.TestActualMoment
import OAI.Combinatorics.SharpRamsey.Entropy.TestSecondMomentBase

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset MeasureTheory SharpRamseyFive.PoissonScore
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedTestActualSecondMoment_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedTestActualSecondMoment_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

def pencilTheta (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ≥0) (H J : Projectivization K (Module.Dual K V)) : ℝ :=
  if H=J then 0 else overlap S x c H J

omit [Finite K] [FiniteDimensional K V] in
lemma family_all_pairs_card (A : Finset (Projectivization K (Module.Dual K V)))
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c : ℝ≥0)
    (a : ℝ) (ha : 0<a) :
    (univ.filter (fun z : A×A => a ≤ pencilTheta S x c z.1 z.2)).card=
      (largePairs S x c a A).card := by
  rw [←Fintype.card_coe,←Fintype.card_coe]
  apply Fintype.card_congr
  refine {
    toFun := fun z => ⟨(z.1.1.1,z.1.2.1),?_⟩
    invFun := fun z => ⟨(⟨z.1.1,?_⟩,⟨z.1.2,?_⟩),?_⟩
    left_inv := fun z => rfl
    right_inv := fun z => rfl }
  · have hc := (mem_filter.mp z.2).2
    have hn : z.1.1.1≠z.1.2.1 := by
      intro he
      simp only [pencilTheta,ite_eq_left he] at hc
      linarith
    exact mem_filter.mpr ⟨mem_product.mpr ⟨z.1.1.2,z.1.2.2⟩,hn,
      by simpa only [pencilTheta,ite_eq_right hn] using hc⟩
  · exact (mem_product.mp (mem_filter.mp z.2).1).1
  · exact (mem_product.mp (mem_filter.mp z.2).1).2
  · apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    simpa only [pencilTheta,ite_eq_right (mem_filter.mp z.2).2.1] using (mem_filter.mp z.2).2.2

omit [Finite K] [FiniteDimensional K V] in
lemma pencilTheta_nonneg (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ≥0) (H J : Projectivization K (Module.Dual K V)) :
    0 ≤ pencilTheta S x c H J := by
  unfold pencilTheta overlap
  split_ifs <;> positivity

lemma pencilTheta_le_mass (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (c : ℝ≥0) (H J : Projectivization K (Module.Dual K V))
    (hH : x.submodule ≤ LinearMap.ker H.rep) (hJ : x.submodule ≤ LinearMap.ker J.rep) :
    pencilTheta S x c H J ≤ mass (radialWeight S x c) (lines x H) := by
  unfold pencilTheta
  split_ifs with he
  · exact mass_nonneg _ _
  · rw [←radialWeight_intersection S x c H J hH hJ]
    exact mass_mono _ inter_subset_left

theorem actual_projective_second_moment
    (j : ℕ) (hdim : Module.finrank K V ≤ j+1)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hA : ∀ H∈A,x.submodule ≤ LinearMap.ker H.rep)
    (f B C : ℝ) (hf : f ≤ 1/4) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (R : ℕ) (own : A → Fin R → Bool) (hL : 1 ≤ (L:ℝ)) (hR : 200 ≤ R)
    (hlow : ∀ H∈A,3/4 ≤ (c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card)
    (hupp : ∀ H∈A,(c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card ≤ 2)
    (hdelta : ∀ H∈A,|(c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f)| ≤ 1)
    (hsq : (∑ H∈A,((c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f))^2) ≤ C*B*Real.exp ((L:ℝ)/100))
    (hcard : ((∑ i∈range j,Nat.card K^i):ℝ) ≤ C*B^2)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i∈T,0<a i)
    (hcover : ∀ H∈A,∀ J∈A,H≠J → 0<overlap S x c H J →
      ∃ i∈T,a i ≤ overlap S x c H J ∧ overlap S x c H J ≤ 2*a i)
    (hcount : ∀ i∈T,((largePairs S x c (a i) A).card:ℝ)*a i^200 ≤ B^2*Real.exp (((L:ℝ)*R)/50))
    (hd : C*2^R ≤ Real.exp ((L:ℝ)*R/20))
    (hp : (2*(L:ℝ)^2)^R ≤ Real.exp ((L:ℝ)*R/25))
    (hb : C^2*Real.exp ((L:ℝ)/50)+(T.card:ℝ)*2^R*Real.exp ((L:ℝ)*R/50) ≤ Real.exp ((L:ℝ)*R/20))
    (h2 : 2 ≤ Real.exp ((L:ℝ)*R/20)) :
    (∫ ω,(∑ H : A,scoreTerm (lines x H) (Real.exp (-(L:ℝ)*(1-f))) (own H)
      (fun r d => ω (r,d)))^2 ∂batchMeasure (fun i : Fin R × RadialLine x => L*radialWeight S x c i.2))
      ≤ B^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R)) := by
  let lam : A → ℝ := fun H => (c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.1.rep)).card
  let θ : A → A → ℝ := fun H J => pencilTheta S x c H J
  have hm (H : A) : mass (radialWeight S x c) (lines x H)=lam H :=
    radialWeight_mass S x c H (hA H H.2)
  have hscaled (D : Finset (RadialLine x)) :
      mass (fun d => L*radialWeight S x c d) D=(L:ℝ)*mass (radialWeight S x c) D := by
    simp only [mass,NNReal.coe_mul,Finset.mul_sum]
  have hs := SharpLogRamsey.SecondMoment.prepared_pencil_second_moment
    (fun d => L*radialWeight S x c d) (fun H : A => lines x H) R own
    (L:ℝ) (1-f) B C lam θ T a hL (by linarith) hB hC hR
    (fun H => by rw [hscaled,hm]) (fun H => hlow H H.2) (fun H => hdelta H H.2)
    (by
      simp only [sq_abs]
      calc
        _ = ∑ H∈A,((c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f))^2 := by
          rw [←Finset.sum_coe_sort A (fun H => ((c:ℝ)*(S.filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f))^2)]
        _ ≤ _ := hsq)
    (by
      rw [Fintype.card_coe]
      exact (Nat.cast_le.mpr (pencil_rank_card j hdim A x hA)).trans (by exact_mod_cast hcard))
    (fun H J => pencilTheta_nonneg S x c H J)
    (fun H J => (pencilTheta_le_mass S x c H J (hA H H.2) (hA J J.2)).trans
      (by rw [hm]; exact hupp H H.2))
    (fun H J hne => by
      rw [hscaled,radialWeight_intersection S x c H J (hA H H.2) (hA J J.2)]
      dsimp [θ,pencilTheta]
      rw [ite_eq_right (fun he => hne (Subtype.ext he))])
    (fun i hi => (ha i hi).le)
    (fun H J hθ => by
      have hne : H.1≠J.1 := by
        intro he
        simp only [θ,pencilTheta,ite_eq_left he] at hθ
        linarith
      simp only [θ,pencilTheta,ite_eq_right hne] at hθ ⊢
      exact hcover H H.2 J J.2 hne hθ)
    (fun i hi => by
      rw [family_all_pairs_card A S x c (a i) (ha i hi)]
      exact hcount i hi)
    hd hp hb h2
  have he := (measurePreserving_uncurry_schedule
    (fun d => L*radialWeight S x c d) R).integral_comp
    (MeasurableEquiv.curry (Fin R) (RadialLine x) ℕ).symm.measurableEmbedding
    (fun ω => (∑ H : A,scoreTerm (lines x H) (Real.exp (-(L:ℝ)*(1-f))) (own H)
      (fun r d => ω (r,d)))^2)
  rw [←he]
  exact hs

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
