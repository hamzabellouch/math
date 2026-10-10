import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Ultrapower.UltraSaturation
import OAI.Analysis.Kaplansky.Ultrapower.PolarDefect
import OAI.Analysis.Kaplansky.Ultrapower.PartialIsometry
import OAI.Analysis.Kaplansky.Ultrapower.CornerPolarCut

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open Filter Topology
open scoped ComplexOrder ENNReal
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (V : QuasiValue A) (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop)

private local instance ultraRealSMulComm :
    SMulCommClass ℝ (V.UltraQuotient u) (V.UltraQuotient u) := Algebra.to_smulCommClass

private local instance ultraRealTower :
    IsScalarTower ℝ (V.UltraQuotient u) (V.UltraQuotient u) := IsScalarTower.right

private local instance ultraRealCFC :
    NonUnitalContinuousFunctionalCalculus ℝ (V.UltraQuotient u) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

private local instance ultraNonnegSpectrum : NonnegSpectrumClass ℝ (V.UltraQuotient u) :=
  CStarAlgebra.instNonnegSpectrumClass

include hu in

lemma ultra_polar_corner (x p q : V.UltraQuotient u) (hp : IsStarProjection p)
    (hxp : x*p=x) (hqx : q*x=x) :
    ∃ v : V.UltraQuotient u, IsPartialIsometry v ∧
      v*CFC.sqrt (star x*x)=x ∧ q*v=v ∧ v*p=v := by
  let : NonUnitalContinuousFunctionalCalculus ℝ (Sequences (A := A) (ι := ℕ)) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (Sequences (A := A) (ι := ℕ)) :=
    CStarAlgebra.instNonnegSpectrumClass
  let W := V.ultra u
  let Q := V.ultraHom u
  let s := CFC.sqrt (star x*x)
  let z : StarTerm (V.UltraQuotient u) := .var
  let sub (a b : StarTerm (V.UltraQuotient u)) := StarTerm.add a (.neg b)
  let P : Fin 4 → StarTerm (V.UltraQuotient u) :=
    ![sub (.mul (.mul z (.star z)) z) z,
      sub (.mul z (.const s)) (.const x),
      sub (.mul (.const q) z) z,
      sub (.mul z (.const p)) z]
  have happ (ε : ℝ) (hε : 0 < ε) : ∃ v : V.UltraQuotient u,
      ‖v‖ ≤ 1 ∧ ∀ j : Fin 4, |V.ultraQ u ((P j).eval id v)-(0:ℝ)| < ε := by
    obtain ⟨a,ha⟩ := W.nullIdeal.mk_surjective x
    change Q a=x at ha
    obtain ⟨r,hr,hdef,herr⟩ := exists_good_polarCut W a (half_pos hε)
    let v := Q (polarCut a r)
    have hvcut : v=polarCut x r := by dsimp only [v]; rw [map_polarCut Q a hr,ha]
    have hnorm : ‖v‖ ≤ 1 :=
      (W.nullIdeal.norm_mk_le (polarCut a r)).trans (polarCut_norm a hr)
    have hsqmap : Q (CFC.sqrt (star a*a))=s := by
      refine (map_cfc_sqrt Q _ (star_mul_self_nonneg a)).trans ?_
      rw [map_mul, map_star, ha]
      rfl
    have hdefmap : W.quotQ (v*star v*v-v)=W.q (polarCut a r*star (polarCut a r)*polarCut a r-polarCut a r) := by
      rw [← W.quotQ_map]
      congr 1

    have herrmap : W.quotQ (v*s-x)=W.q (polarCut a r*CFC.sqrt (star a*a)-a) := by
      rw [← W.quotQ_map]
      congr 1
      change v*s-x=Q (polarCut a r*CFC.sqrt (star a*a)-a)
      rw [map_sub,map_mul,hsqmap,ha]

    refine ⟨v,hnorm,?_⟩
    intro j
    fin_cases j <;> simp [P,sub,z,StarTerm.eval,← sub_eq_add_neg]
    · change |W.quotQ (v*star v*v-v)| < ε
      rw [abs_of_nonneg (W.quotQ_nonneg _),hdefmap]
      exact hdef.trans (by linarith)
    · change |W.quotQ (v*s-x)| < ε
      rw [abs_of_nonneg (W.quotQ_nonneg _),herrmap]
      exact ((W.q_bound _).trans herr).trans_lt (by linarith)
    · change |W.quotQ (q*v-v)| < ε
      have he : q*v=v := hvcut ▸ polarCut_left_corner hqx r
      rw [he,sub_self,W.quotQ_zero,abs_zero]
      exact hε
    · change |W.quotQ (v*p-v)| < ε
      have he : v*p=v := hvcut ▸ polarCut_right_corner hp hxp r
      rw [he,sub_self,W.quotQ_zero,abs_zero]
      exact hε
  obtain ⟨v,hv⟩ := V.ultra_realize u hu P (fun _ => 0) happ
  have he0 := hv 0
  have he1 := hv 1
  have he2 := hv 2
  have he3 := hv 3
  simp [P,sub,z,StarTerm.eval,← sub_eq_add_neg] at he0 he1 he2 he3
  have h0 : v*star v*v-v=0 := (W.quotQ_eq_zero _).mp he0
  have h1 : v*s-x=0 := (W.quotQ_eq_zero _).mp he1
  have h2 : q*v-v=0 := (W.quotQ_eq_zero _).mp he2
  have h3 : v*p-v=0 := (W.quotQ_eq_zero _).mp he3
  exact ⟨v,sub_eq_zero.mp h0,sub_eq_zero.mp h1,sub_eq_zero.mp h2,sub_eq_zero.mp h3⟩

include hu in
lemma ultra_polar (x : V.UltraQuotient u) : ∃ v : V.UltraQuotient u,
    IsPartialIsometry v ∧ v*CFC.sqrt (star x*x)=x := by
  obtain ⟨v,hv,hvx,_,_⟩ := V.ultra_polar_corner u hu x 1 1 (IsStarProjection.one _) (mul_one x) (one_mul x)
  exact ⟨v,hv,hvx⟩


end KaplanskyConsequences.QuasiValue

end

end OAI
