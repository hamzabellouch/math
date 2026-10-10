import OAI.Analysis.CircleDomains.Sobolev.AdmissibleL2Convex
import OAI.Analysis.CircleDomains.Sobolev.HilbertWeakConvexApproximation
import OAI.Analysis.CircleDomains.Probability.MeasureFamilySignedLimit

namespace OAI

/-! A weak L² limit of nonnegative densities satisfying increasing
pointwise constraints bounds the modulus of their union. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

lemma measureFamilyModulus_le_weak_limit
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) (K : A → FiniteMeasure Z)
    (S : ℕ → Set A) (hcover : ∀ a, ∀ᶠ n in atTop, a ∈ S n)
    (u : ℕ → Lp ℝ 2 σ) (v : Lp ℝ 2 σ)
    (hu : ∀ n, ∀ᶠ k in atTop, u k ∈ admissibleL2Classes σ (fun a : S n => K a.val))
    (hw : ∀ w : Lp ℝ 2 σ, Tendsto (fun n => inner ℝ (u n) w) atTop (𝓝 (inner ℝ v w))) :
    measureFamilyModulus A Z σ K ≤ ENNReal.ofReal (‖v‖^2) := by
  obtain ⟨a,ha,hav⟩ := exists_strong_approximation_of_convex_eventual_constraints
    (fun n => admissibleL2Classes σ (fun b : S n => K b.val))
    (fun n => admissibleL2Classes_convex σ _) hu hw
  choose f hf hfm hf0 hfa heq using ha
  have heLp : Tendsto (fun n => eLpNorm (fun z => f n z-v z) 2 σ) atTop (𝓝 0) := by
    have hh := hav.edist (tendsto_const_nhds (x := v))
    simp only [edist_self] at hh
    convert hh using 1
    funext n
    calc
      eLpNorm (fun z => f n z-v z) 2 σ =
          edist ((hf n).toLp (f n)) ((Lp.memLp v).toLp v) :=
        (Lp.edist_toLp_toLp (f n) v (hf n) (Lp.memLp v)).symm
      _ = edist (a n) v := by rw [heq n,Lp.toLp_coeFn]
  have hb := measureFamilyModulus_le_of_signed_L2_limit σ K f v hfm hf0 hf
    (Lp.stronglyMeasurable v).measurable (Lp.memLp v) heLp (fun b =>
      (hcover b).mono (fun n hn => hfa n ⟨b,hn⟩))
  simpa only [Lp.toLp_coeFn] using hb

end CircleDomainRigidity

end

end OAI
