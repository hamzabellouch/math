import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConnectedSolvableUnipotence
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommonEigencharacterTorsion
import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntertwinedUnipotence

namespace OAI

/-! # Connected solvable actions with unipotent powers

Finite generation makes a torsion eigencharacter finite. Its kernel is dense
in the connected polynomial topology, so the whole common eigenspace is
fixed. Quotient-dimension induction then bounds all mixed operator words.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

open scoped commutatorElement

variable {K G : Type*} [Field K] [Group G]

theorem isClosed_vector_fixer {n : ℕ} (v : Fin n → K) :
    IsClosed {g : PolynomialMatrixGroup K n | linearAction g v = v} := by
  have he : {g : PolynomialMatrixGroup K n | linearAction g v = v} =
      ⋂ i : Fin n, {g | (linearAction g v) i = v i} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
  rw [he]
  apply isClosed_iInter
  intro i
  let p := functionalPolynomial (LinearMap.proj i) v - MvPolynomial.C (v i)
  have hc := (AffinePolynomialPoint.isClosed_zeroSet p).preimage
    inducing_coordinates.continuous
  simpa only [p, Set.preimage_ofPred_eq, map_sub, MvPolynomial.eval_C,
    eval_functionalPolynomial, LinearMap.proj_apply, sub_eq_zero] using hc

theorem connected_commonEigenspace_fixed
    [TopologicalSpace G] [PreconnectedSpace G] [SeparatelyContinuousMul G]
    [ContinuousInv G] [Group.FG G] {n : ℕ}
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι)
    (χ : G → K)
    (hχ : commonEigenspace (fun g => (linearAction (ι g)).toLinearMap) χ ≠ ⊥)
    (hρ : ∀ g, ∃ m : ℕ, 0 < m ∧ IsNilpotent ((linearAction (ι g)).toLinearMap ^ m - 1)) :
    ∀ g v, v ∈ commonEigenspace (fun g => (linearAction (ι g)).toLinearMap) χ →
      linearAction (ι g) v = v := by
  let ρ := linearAction.toMonoidHom.comp ι
  obtain ⟨ξ, hξ, hfin⟩ := commonEigenspace_finite_character ρ χ hχ hρ
  let : Finite ξ.range := hfin
  intro g v hv
  have hclosed : IsClosed {g : G | linearAction (ι g) v = v} :=
    (isClosed_vector_fixer v).preimage hι
  have hsub : (ξ.ker : Set G) ⊆ {g : G | linearAction (ι g) v = v} := by
    intro a ha
    have ha' : ξ a = 1 := ha
    have he := (mem_commonEigenspace _ _ _).mp hv a
    change linearAction (ι a) v = χ a • v at he
    rw [← hξ, ha', Units.val_one, one_smul] at he
    exact he
  have hclosure := closure_minimal hsub hclosed
  apply hclosure
  change g ∈ separateClosure ξ.ker
  rw [separateClosure_eq_top_of_finiteIndex ξ.ker]
  trivial

theorem connected_solvable_quasiUnipotent_words
    [IsAlgClosed K] [TopologicalSpace G] [PreconnectedSpace G]
    [SeparatelyContinuousMul G] [ContinuousInv G] [Group.FG G] [Group.IsSolvable G]
    {n : ℕ}
    (hc₁ : ∀ g : G, Continuous (fun h : G => ⁅g, h⁆))
    (hc₂ : ∀ h : G, Continuous (fun g : G => ⁅g, h⁆))
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι)
    (hρ : ∀ g, ∃ m : ℕ, 0 < m ∧ IsNilpotent ((linearAction (ι g)).toLinearMap ^ m - 1)) :
    ∃ c : ℕ, ∀ w : List G, w.length = c →
      actionOperatorWord (fun a : G => (linearAction (ι a)).toLinearMap - 1) w = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      refine ⟨0, fun _ _ => ?_⟩
      ext v i
      exact Fin.elim0 i
    let : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    obtain ⟨χ, hχ⟩ := connected_solvable_commonEigenspace hc₁ hc₂ ι hι
    let ρ := linearAction.toMonoidHom.comp ι
    let W := commonEigenspace (fun g => (ρ g).toLinearMap) χ
    have hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W := commonEigenspace_invariant ρ χ
    have hfix : ∀ g v, v ∈ W → ρ g v = v :=
      connected_commonEigenspace_fixed ι hι χ hχ hρ
    let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hχ
    let m := Module.finrank K ((Fin n → K) ⧸ W)
    have hm : m < n := by
      have he := W.finrank_quotient_add_finrank
      have hp := Module.finrank_pos (R := K) (M := W)
      rw [Module.finrank_fin_fun] at he
      change m + Module.finrank K W = n at he
      omega
    let e := (Module.finBasis K ((Fin n → K) ⧸ W)).equivFun
    let ρQ := quotientLinearAction ρ W hW
    let ιQ : G →* PolynomialMatrixGroup K m := coordinateLinearAction ρQ e
    have hιQ : Continuous ιQ := continuous_quotientLinearAction ι hι W hW e
    let q : (Fin n → K) →ₗ[K] (Fin m → K) := e.toLinearMap.comp W.mkQ
    have hq : Function.Surjective q := e.surjective.comp W.mkQ_surjective
    have hi (g : G) (v : Fin n → K) :
        q (ρ g v) = linearAction (ιQ g) (q v) := by
      rw [coordinateLinearAction_apply]
      change e (W.mkQ (ρ g v)) = e (ρQ g (e.symm (e (W.mkQ v))))
      rw [e.symm_apply_apply]
      rfl
    have hρQ (g : G) : ∃ k : ℕ, 0 < k ∧
        IsNilpotent ((linearAction (ιQ g)).toLinearMap ^ k - 1) :=
      unipotent_power_of_surjective_intertwining q hq _ _ (hi g) (hρ g)
    obtain ⟨c, hc⟩ := ih m hm ιQ hιQ hρQ
    let D := fun a : G => (ρ a).toLinearMap - 1
    let E := fun a : G => (linearAction (ιQ a)).toLinearMap - 1
    have hint (a : G) (v : Fin n → K) : q (D a v) = E a (q v) := by
      change q (ρ a v - v) = linearAction (ιQ a) (q v) - q v
      rw [map_sub, hi]
    refine ⟨c + 1, ?_⟩
    intro w hw
    cases w with
    | nil => simp only [List.length_nil] at hw; omega
    | cons a w =>
      have hw' : w.length = c := by simp only [List.length_cons] at hw; omega
      have hz : actionOperatorWord E w = 0 := hc w hw'
      apply LinearMap.ext
      intro v
      change ρ a (actionOperatorWord D w v) - actionOperatorWord D w v = 0
      apply sub_eq_zero.mpr
      apply hfix
      apply (Submodule.Quotient.mk_eq_zero W).mp
      apply e.injective
      have hqv := actionOperatorWord_intertwines D E q hint w v
      rw [hz] at hqv
      simpa only [q, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply,
        LinearMap.zero_apply, map_zero] using hqv

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
