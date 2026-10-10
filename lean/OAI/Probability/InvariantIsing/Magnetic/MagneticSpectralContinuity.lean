import OAI.Probability.InvariantIsing.Magnetic.MagneticPopulationContinuity
import OAI.Probability.InvariantIsing.Spectral.FiniteSpectralContinuity

namespace OAI

/-! Uniform spectral-transform errors pass through both magnetic
optimizations, and imply continuity in positive spectral populations. -/
noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace InvariantIsing

lemma magneticVariationalFunctional_le_add {A : Type*} [Fintype A]
    (γ mag : A → ℝ) (R Q : ℝ → ℝ) (hR : Continuous R) (hQ : Continuous Q)
    (δ : ℝ) (hδ : ∀ x ∈ Set.Icc (0 : ℝ) 1, |R x - Q x| ≤ δ) :
    magneticVariationalFunctional R γ mag ≤ magneticVariationalFunctional Q γ mag + ((δ / 2 : ℝ) : EReal) := by
  apply (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
    (.inl (EReal.coe_ne_top _))).mp
  apply le_iInf
  intro p
  apply (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
    (.inl (EReal.coe_ne_top _))).mpr
  have hspec : (spectralFunctional R p : EReal) ≤
      (spectralFunctional Q p : EReal) + ((δ / 2 : ℝ) : EReal) := by
    rw [← EReal.coe_add]
    apply EReal.coe_le_coe
    have hb := (abs_le.mp (abs_spectralFunctional_sub_le R Q hR hQ δ hδ p)).2
    linarith
  calc
    magneticVariationalFunctional R γ mag ≤ magneticEntropyFunctional γ mag p + (spectralFunctional R p : EReal) :=
      iInf_le _ p
    _ ≤ magneticEntropyFunctional γ mag p +
        ((spectralFunctional Q p : EReal) + ((δ / 2 : ℝ) : EReal)) :=
      add_le_add le_rfl hspec
    _ = _ := by rw [add_assoc]


lemma finiteMagneticFunctional_spectral_le_add {A : Type*} [Fintype A]
    (γ b : A → ℝ) (R Q : ℝ → ℝ) (hR : Continuous R) (hQ : Continuous Q)
    (δ : ℝ) (hδ : ∀ x ∈ Icc (0 : ℝ) 1, |R x-Q x| ≤ δ) :
    finiteMagneticFunctional R γ b ≤ finiteMagneticFunctional Q γ b+((δ/2 : ℝ) : EReal) := by
  apply iSup_le
  intro mag
  have hh := magneticVariationalFunctional_le_add γ (fun a => (mag.val a : ℝ)) R Q hR hQ δ hδ
  have hi := le_iSup (fun t : RationalMagnetization A =>
    ((∑ a, γ a*b a*(t.val a : ℝ) : ℝ) : EReal)+
      magneticVariationalFunctional Q γ (fun a => (t.val a : ℝ))) mag
  calc
    _ ≤ ((∑ a, γ a*b a*(mag.val a : ℝ) : ℝ) : EReal)+
        (magneticVariationalFunctional Q γ (fun a => (mag.val a : ℝ))+((δ/2 : ℝ) : EReal)) :=
      add_le_add le_rfl hh
    _ = (((∑ a, γ a*b a*(mag.val a : ℝ) : ℝ) : EReal)+
        magneticVariationalFunctional Q γ (fun a => (mag.val a : ℝ)))+((δ/2 : ℝ) : EReal) :=
      (add_assoc _ _ _).symm
    _ ≤ _ := add_le_add hi le_rfl

theorem finiteMagneticFunctional_tendsto_weights {A ι : Type*} [Fintype A] [Fintype ι]
    (ρs : ℕ → ι → ℝ) (ρ eig : ι → ℝ)
    (hspos : ∀ k a, 0 < ρs k a) (hssum : ∀ k, ∑ a, ρs k a=1)
    (hpos : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (hρs : Tendsto ρs atTop (𝓝 ρ))
    (γ b : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1) :
    Tendsto (fun k => (finiteMagneticFunctional (finiteR (ρs k) eig (hspos k) (hssum k)) γ b).toReal)
      atTop (𝓝 (finiteMagneticFunctional (finiteR ρ eig hpos hsum) γ b).toReal) := by
  have hr := finiteVariational_ne_top_bot ρ eig hpos hsum
  have hf := finiteMagneticFunctional_ne_top_bot _ γ b hγ hγsum hr.1 hr.2
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [finiteR_uniform_weights ρs ρ eig hspos hssum hpos hsum hρs ε hε] with k hk
  have hrk := finiteVariational_ne_top_bot (ρs k) eig (hspos k) (hssum k)
  have hfk := finiteMagneticFunctional_ne_top_bot _ γ b hγ hγsum hrk.1 hrk.2
  have hleft := finiteMagneticFunctional_spectral_le_add γ b
    (finiteR (ρs k) eig (hspos k) (hssum k)) (finiteR ρ eig hpos hsum)
    (continuous_finiteR (ρs k) eig (hspos k) (hssum k)) (continuous_finiteR ρ eig hpos hsum)
    ε (fun x hx => (hk x hx).le)
  have hright := finiteMagneticFunctional_spectral_le_add γ b
    (finiteR ρ eig hpos hsum) (finiteR (ρs k) eig (hspos k) (hssum k))
    (continuous_finiteR ρ eig hpos hsum) (continuous_finiteR (ρs k) eig (hspos k) (hssum k))
    ε (fun x hx => by simpa only [abs_sub_comm] using (hk x hx).le)
  rw [← EReal.coe_toReal hfk.1 hfk.2,← EReal.coe_toReal hf.1 hf.2,
    ← EReal.coe_add,EReal.coe_le_coe_iff] at hleft hright
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

end InvariantIsing

end

end OAI
