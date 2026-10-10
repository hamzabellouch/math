import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace Problem336AdditiveD139
namespace BrownianBridge

variable {Ω : Type u_1} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

lemma independent_processes_jointGaussian {I : Type u_2} {T : Type u_3} (X : I → T → Ω → ℝ)
    (hX : ∀ i, IsGaussianProcess (X i) P)
    (hInd : iIndepFun (fun i ω s => X i s ω) P) :
    IsGaussianProcess (fun p : I × T => X p.1 p.2) P := by
  classical
  constructor
  intro S
  let K := S.image Prod.fst
  let J := S.image Prod.snd
  have hInd' := (iIndepFun.precomp (g := fun i : K => i.val) Subtype.val_injective hInd).comp
    (fun _ (x : T → ℝ) (s : J) => x s) (by fun_prop)
  have hG := hInd'.hasGaussianLaw (fun i : K => (hX i).hasGaussianLaw J)
  let L : (K → J → ℝ) →L[ℝ] (S → ℝ) :=
    { toFun := fun x p => x ⟨p.val.1, Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩⟩
          ⟨p.val.2, Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact hG.map L

def bridge (B : ℝ≥0 → Ω → ℝ) (t s : ℝ≥0) (ω : Ω) : ℝ :=
  B s ω - (s : ℝ) / (t : ℝ) * B t ω

lemma bridge_aemeasurable (hB : IsPreBrownianReal B P) (t s : ℝ≥0) :
    AEMeasurable (bridge B t s) P :=
  (hB.aemeasurable s).sub ((hB.aemeasurable t).const_mul _)

lemma bridge_endpoint_jointGaussian (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    IsGaussianProcess
      (Sum.elim (fun s : Set.Iic t => bridge B t s) (fun _ : Unit => B t)) P := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro u
  cases u with
  | inl s =>
    refine ⟨{s.val, t},
      { toFun := fun x => x ⟨s.val, by simp⟩ -
          (s.val : ℝ) / (t : ℝ) * x ⟨t, by simp⟩
        map_add' := ?_
        map_smul' := ?_ }, ?_⟩
    · intro x y
      simp
      ring
    · intro c x
      simp
      ring
    · intro ω
      rfl
  | inr u =>
    refine ⟨{t},
      { toFun := fun x => x ⟨t, by simp⟩
        map_add' := by simp
        map_smul' := by simp }, ?_⟩
    intro ω
    rfl

lemma bridge_endpoint_covariance (hB : IsPreBrownianReal B P)
    {t s : ℝ≥0} (ht : 0 < t) (hs : s ≤ t) :
    cov[bridge B t s, B t; P] = 0 := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hL (u : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval u).memLp_two
  change cov[fun ω => B s ω - (s : ℝ) / (t : ℝ) * B t ω, B t; P] = 0
  rw [covariance_fun_sub_left (hL s) ((hL t).const_mul _) (hL t),
    covariance_const_mul_left, hB.covariance_eval, hB.covariance_eval,
    min_eq_left hs, min_self]
  have htr : (t : ℝ) ≠ 0 := ne_of_gt (show (0 : ℝ) < t from ht)
  simp [div_mul_cancel₀ _ htr]

theorem bridge_indep_endpoint (hB : IsPreBrownianReal B P)
    {t : ℝ≥0} (ht : 0 < t) :
    IndepFun (fun ω (s : Set.Iic t) => bridge B t s ω) (B t) P := by
  have h := (bridge_endpoint_jointGaussian hB t).indepFun_of_covariance_eq_zero
    (fun s => bridge_aemeasurable hB t s)
    (fun _ => hB.aemeasurable t)
    (fun s _ => bridge_endpoint_covariance hB ht s.property)
  exact h.comp measurable_id (measurable_pi_apply ())

lemma family_bridge_endpoint_jointGaussian {I : Type u_4} (B : I → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hInd : iIndepFun (fun i ω s => B i s ω) P) (t : ℝ≥0) :
    IsGaussianProcess
      (Sum.elim (fun p : I × Set.Iic t => bridge (B p.1) t p.2)
        (fun i : I => B i t)) P := by
  classical
  apply (independent_processes_jointGaussian B
    (fun i => (hB i).isGaussianProcess) hInd).of_isGaussianProcess
  intro u
  cases u with
  | inl p =>
    refine ⟨{(p.1, p.2.val), (p.1, t)},
      { toFun := fun x => x ⟨(p.1, p.2.val), by simp⟩ -
          (p.2.val : ℝ) / (t : ℝ) * x ⟨(p.1, t), by simp⟩
        map_add' := ?_
        map_smul' := ?_ }, ?_⟩
    · intro x y
      simp
      ring
    · intro c x
      simp
      ring
    · intro ω
      rfl
  | inr i =>
    refine ⟨{(i, t)},
      { toFun := fun x => x ⟨(i, t), by simp⟩
        map_add' := by simp
        map_smul' := by simp }, ?_⟩
    intro ω
    rfl

theorem family_bridge_indep_endpoints {I : Type u_5} (B : I → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hInd : iIndepFun (fun i ω s => B i s ω) P) {t : ℝ≥0} (ht : 0 < t) :
    IndepFun (fun ω (p : I × Set.Iic t) => bridge (B p.1) t p.2 ω)
      (fun ω i => B i t ω) P := by
  apply (family_bridge_endpoint_jointGaussian B hB hInd t).indepFun_of_covariance_eq_zero
    (fun p => bridge_aemeasurable (hB p.1) t p.2)
    (fun i => (hB i).aemeasurable t)
  intro p j
  by_cases hij : p.1 = j
  · subst j
    exact bridge_endpoint_covariance (hB p.1) ht p.2.property
  · have h := (hInd.indepFun hij).comp
      (show Measurable (fun x : ℝ≥0 → ℝ => x p.2 - (p.2.val : ℝ) / (t : ℝ) * x t) by
        fun_prop)
      (measurable_pi_apply t)
    exact h.covariance_eq_zero
      (((hB p.1).isGaussianProcess.hasGaussianLaw_eval p.2).memLp_two.sub
        (((hB p.1).isGaussianProcess.hasGaussianLaw_eval t).memLp_two.const_mul _))
      ((hB j).isGaussianProcess.hasGaussianLaw_eval t).memLp_two

end BrownianBridge
end Problem336AdditiveD139

end

end OAI
