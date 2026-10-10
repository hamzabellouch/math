import OAI.Analysis.KadisonKastler.RemoteScalingConjugations

namespace OAI

/-! # Strong centrality from local commutation and state scaling

The local algebras may contain an arbitrary first tensor factor; only
their density on the reference vector is used.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem local_scaling_commutator_tendsto
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (B : ℕ → StarSubalgebra ℂ (H →L[ℂ] H))
    (hB : ∀ k, B k ≤ M.toStarSubalgebra)
    (hdense : ∀ a : Algebra M, ∀ ε : ℝ, 0 < ε →
      ∃ k, ∃ b : B k, ‖a.val Ω-b.val Ω‖ < ε)
    (s : ℕ → ℝ) (v : ℕ → Algebra M)
    (hv : ∀ n, v n*star (v n)=1)
    (hs : ∀ n, StateScales M Ω (s n) (v n).val)
    (hs1 : ∀ n, s n ≤ 1)
    (hcomm : ∀ k, ∀ b : B k, ∀ n, k ≤ n → Commute b.val (v n).val)
    (a : Algebra M) (η : H) :
    Tendsto (fun n => (a*v n-v n*a).val η) atTop (𝓝 0) := by
  have hbound (n : ℕ) : ‖a*v n-v n*a‖ ≤ 2*‖a‖ := by
    have hn := coisometry_norm_le (v n) (hv n)
    calc
      _ ≤ ‖a*v n‖+‖v n*a‖ := norm_sub_le _ _
      _ ≤ ‖a‖*‖v n‖+‖v n‖*‖a‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 2*‖a‖ := by nlinarith [norm_nonneg a]
  apply algebra_strong_tendsto_of_reference Ω
    (commutant_cyclic_of_separating_reference Ω hsep)
    (fun n => a*v n-v n*a) (2*‖a‖) (by positivity) hbound ?_ η
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k,b,hb⟩ := hdense a (ε/3) (by positivity)
  let bM : Algebra M := ⟨b.val,hB k b.property⟩
  filter_upwards [eventually_ge_atTop k] with n hn
  have hc : Commute bM (v n) := Subtype.ext (hcomm k b n hn).eq
  have he := (hs n).coisometry_commutator_bound (v n) (hv n) (hs1 n) a bM hc
  have hb' : ‖(a-bM).val Ω‖ < ε/3 := hb
  have hh : ‖(a*v n-v n*a).val Ω‖ < ε := he.trans_lt (by linarith)
  simpa only [dist_zero_right] using hh

theorem local_scaling_adjoint_commutator_tendsto
    (d : ModularConjugationData M Ω)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (B : ℕ → StarSubalgebra ℂ (H →L[ℂ] H))
    (hB : ∀ k, B k ≤ M.toStarSubalgebra)
    (hdense : ∀ a : Algebra M, ∀ ε : ℝ, 0 < ε →
      ∃ k, ∃ b : B k, ‖a.val Ω-b.val Ω‖ < ε)
    (s : ℕ → ℝ) (v : ℕ → Algebra M)
    (hv : ∀ n, v n*star (v n)=1)
    (hs : ∀ n, StateScales M Ω (s n) (v n).val)
    (hcomm : ∀ k, ∀ b : B k, ∀ n, k ≤ n → Commute b.val (v n).val)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hcs : ∀ᶠ n in atTop, c ≤ s n)
    (a : Algebra M) (η : H) :
    Tendsto (fun n => (a*star (v n)-star (v n)*a).val η) atTop (𝓝 0) := by
  have hbound (n : ℕ) : ‖a*star (v n)-star (v n)*a‖ ≤ 2*‖a‖ := by
    have hn : ‖star (v n)‖ ≤ 1 := by rw [norm_star]; exact coisometry_norm_le _ (hv n)
    calc
      _ ≤ ‖a*star (v n)‖+‖star (v n)*a‖ := norm_sub_le _ _
      _ ≤ ‖a‖*‖star (v n)‖+‖star (v n)‖*‖a‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 2*‖a‖ := by nlinarith [norm_nonneg a]
  apply algebra_strong_tendsto_of_reference Ω
    (commutant_cyclic_of_separating_reference Ω hsep)
    (fun n => a*star (v n)-star (v n)*a) (2*‖a‖) (by positivity) hbound ?_ η
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hden : 0 < 2*(1+c) := by positivity
  obtain ⟨k,b,hb⟩ := hdense a (ε*c/(2*(1+c))) (by positivity)
  let bM : Algebra M := ⟨b.val,hB k b.property⟩
  filter_upwards [hcs,eventually_ge_atTop k] with n hcn hn
  have hcv : Commute (star bM) (v n) :=
    Subtype.ext (hcomm k ⟨star b.val,(B k).star_mem' b.property⟩ n hn).eq
  have hcvstar : Commute bM (star (v n)) := hcv.star_right
  have he := (hs n).coisometry_adjoint_commutator_bound d hc hc1 hcn
    (v n) (hv n) a bM hcvstar
  have hb' : ‖(a-bM).val Ω‖ < ε*c/(2*(1+c)) := hb
  have hm := (lt_div_iff₀ hden).mp hb'
  have hh : ‖(a*star (v n)-star (v n)*a).val Ω‖ < ε := by nlinarith
  simpa only [dist_zero_right] using hh

end

end KadisonKastler

end OAI
