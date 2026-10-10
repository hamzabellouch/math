import Mathlib
import OAI.Probability.Ballisticity.Estimates.CellCertificates

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma cell_bad_event_subset {d k : ℕ} (ν : Measure (Row d))
    (e f : Direction d) (hef : e.1 ≠ f.1) (a C c g₀ g₁ A G : ℝ) (hc : 0 < c)
    (hA : 0 ≤ A) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (v w m s : ℕ) (hv : 2*cellWidth w m 0 ≤ v) (hs : 0 < s)
    (hG : ∀ i < m, G ≤ c*cellRadius ν e f C w m i/2) (q : ℝ≥0∞) :
    {ω | ∃ t : ℕ, v ≤ t ∧ t ≤ v+w ∧
      rawTupleMixture (realPosition (step e)) t (π ω).val ω {y | TupleSeparated f G y} <
        q*(ENNReal.ofReal g₀*ENNReal.ofReal g₁*ENNReal.ofReal (Real.exp (-A*k*m)))} ⊆
    {ω | ∃ h : ℕ, rawTupleMixture (realPosition (step e)) h (π ω).val ω Set.univ < q} ∪
      (⋃ i, scheduledCellSuccess ν e f hef a C c g₀ g₁ A hc π v w m s i)ᶜ := by
  intro ω hω
  by_cases hmass : ω ∈ {ω | ∃ h : ℕ, rawTupleMixture (realPosition (step e)) h (π ω).val ω Set.univ < q}
  · exact Or.inl hmass
  · refine Or.inr ?_
    intro hcert
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hcert
    have him : i < m := by
      by_contra hh
      simp only [scheduledCellSuccess,ite_eq_right hh,Set.mem_empty_iff_false] at hi
    obtain ⟨t,hvt,ht,hbad⟩ := hω
    have hq : q ≤ rawTupleMixture (realPosition (step e)) (cellOpportunity v w m i) (π ω).val ω Set.univ := by
      by_contra hh
      exact hmass ⟨_,not_le.mp hh⟩
    have hp := successful_cell_certificate ν e f hef a C c g₀ g₁ A hc hA π v w m s i hv hs ω hi t hvt ht
    have hmono : rawTupleMixture (realPosition (step e)) t (π ω).val ω
        {y | TupleSeparated f (c*cellRadius ν e f C w m i/2) y} ≤
      rawTupleMixture (realPosition (step e)) t (π ω).val ω {y | TupleSeparated f G y} := by
      apply measure_mono
      intro y hy j l hjl
      exact (hG i him).trans (hy j l hjl)
    exact (not_lt_of_ge ((mul_le_mul_left hq _).trans (hp.trans hmono))) hbad

lemma cells_bad_probability {d k n : ℕ} (ν : Measure (Row d))
    (e f : Direction d) (hef : e.1 ≠ f.1) (a C c g₀ g₁ A : ℝ) (hc : 0 < c)
    (hA : 0 ≤ A) (π : Environment d → LayerTupleProfile (k:=k) e a)
    (v w : Fin n → ℕ) (m s : ℕ) (hs : 0 < s) (G : Fin n → ℝ)
    (hv : ∀ j, 2*cellWidth (w j) m 0 ≤ v j)
    (hG : ∀ j i, i < m → G j ≤ c*cellRadius ν e f C (w j) m i/2)
    (q δ ε : ℝ≥0∞)
    (hmass : environmentLaw ν {ω | ∃ h : ℕ, rawTupleMixture (realPosition (step e)) h (π ω).val ω Set.univ < q} ≤ δ)
    (hcell : ∀ j, environmentLaw ν (⋃ i, scheduledCellSuccess ν e f hef a C c g₀ g₁ A hc π (v j) (w j) m s i)ᶜ ≤ ε) :
    environmentLaw ν {ω | ∃ j : Fin n, ∃ t : ℕ, v j ≤ t ∧ t ≤ v j+w j ∧
      rawTupleMixture (realPosition (step e)) t (π ω).val ω {y | TupleSeparated f (G j) y} <
        q*(ENNReal.ofReal g₀*ENNReal.ofReal g₁*ENNReal.ofReal (Real.exp (-A*k*m)))} ≤ δ+n*ε := by
  let E := {ω | ∃ h : ℕ, rawTupleMixture (realPosition (step e)) h (π ω).val ω Set.univ < q}
  let F := fun j : Fin n => (⋃ i, scheduledCellSuccess ν e f hef a C c g₀ g₁ A hc π (v j) (w j) m s i)ᶜ
  have hsub : {ω | ∃ j : Fin n, ∃ t : ℕ, v j ≤ t ∧ t ≤ v j+w j ∧
      rawTupleMixture (realPosition (step e)) t (π ω).val ω {y | TupleSeparated f (G j) y} <
        q*(ENNReal.ofReal g₀*ENNReal.ofReal g₁*ENNReal.ofReal (Real.exp (-A*k*m)))} ⊆ E ∪ ⋃ j, F j := by
    rintro ω ⟨j,hj⟩
    rcases cell_bad_event_subset ν e f hef a C c g₀ g₁ A (G j) hc hA π (v j) (w j) m s (hv j) hs (hG j) q hj with he|hf
    · exact Or.inl he
    · exact Or.inr (Set.mem_iUnion.mpr ⟨j,hf⟩)
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  apply add_le_add hmass
  apply (measure_iUnion_fintype_le _ _).trans
  calc
    ∑ j : Fin n, environmentLaw ν (F j) ≤ ∑ _j : Fin n, ε := Finset.sum_le_sum (fun j _ => hcell j)
    _ = n*ε := by simp [nsmul_eq_mul]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

def stageBadEvent {d k : ℕ} (e f : Direction d) (H : ℕ) (Gminus Gplus : ℝ)
    (π : Measure (Fin k → Lattice d)) (p : ℝ≥0∞) : Set (Environment d) :=
  {ω | (∃ h : ℕ, 1 ≤ h ∧ h ≤ H ∧
      rawTupleMixture (realPosition (step e)) h π ω {y | TupleSeparated f Gminus y} < p) ∨
    rawTupleMixture (realPosition (step e)) H π ω {y | TupleSeparated f Gplus y} < p}

theorem finite_stage_assembly {d k n : ℕ} (ν : Measure (Row d))
    (e f : Direction d) (hef : e.1 ≠ f.1) (a C c g₀ g₁ A G Gminus Gplus r : ℝ)
    (hc : 0 < c) (hA : 0 ≤ A) (π : BudgetProfile (k:=k) e f a G)
    (He H : ℕ) (v w : Fin n → ℕ) (m s : ℕ) (hs : 0 < s) (Gs : Fin n → ℝ)
    (hv : ∀ j, 2*cellWidth (w j) m 0 ≤ v j)
    (hGs : ∀ j i, i < m → Gs j ≤ c*cellRadius ν e f C (w j) m i/2)
    (hcover : ∀ h : ℕ, He < h → h ≤ H → ∃ j, v j ≤ h ∧ h ≤ v j+w j ∧ Gminus ≤ Gs j)
    (hgrowth : ∃ j, v j ≤ H ∧ H ≤ v j+w j ∧ Gplus ≤ Gs j)
    (hshortgap : Gminus ≤ G-r) (p q δ₀ δ₁ ε : ℝ≥0∞)
    (hp : p ≤ q*(ENNReal.ofReal g₀*ENNReal.ofReal g₁*ENNReal.ofReal (Real.exp (-A*k*m))))
    (hshort : environmentLaw ν {ω | relativeBudgetMassENN e f He r π.val ω < p} ≤ δ₀)
    (hmass : environmentLaw ν {ω | ∃ h : ℕ, rawTupleMixture (realPosition (step e)) h π.val ω Set.univ < q} ≤ δ₁)
    (hcell : ∀ j, environmentLaw ν (⋃ i, scheduledCellSuccess ν e f hef a C c g₀ g₁ A hc
      (fun _ => π.toLayerProfile) (v j) (w j) m s i)ᶜ ≤ ε) :
    environmentLaw ν (stageBadEvent e f H Gminus Gplus π.val p) ≤ δ₀+δ₁+n*ε := by
  let E := {ω | relativeBudgetMassENN e f He r π.val ω < p}
  let F := {ω | ∃ j : Fin n, ∃ t : ℕ, v j ≤ t ∧ t ≤ v j+w j ∧
      rawTupleMixture (realPosition (step e)) t π.val ω {y | TupleSeparated f (Gs j) y} <
        q*(ENNReal.ofReal g₀*ENNReal.ofReal g₁*ENNReal.ofReal (Real.exp (-A*k*m)))}
  have hF : environmentLaw ν F ≤ δ₁+n*ε :=
    cells_bad_probability ν e f hef a C c g₀ g₁ A hc hA (fun _ => π.toLayerProfile)
      v w m s hs Gs hv hGs q δ₁ ε hmass hcell
  have hsub : stageBadEvent e f H Gminus Gplus π.val p ⊆ E ∪ F := by
    intro ω hω
    rcases hω with ⟨h,hh,hH,hbad⟩|hbad
    · by_cases he : h ≤ He
      · apply Or.inl
        apply lt_of_le_of_lt _ hbad
        have hb := budget_profile_prefix_certificate e f a G r π ω h He he
        apply hb.trans
        exact measure_mono (fun y hy j l hjl => hshortgap.trans (hy j l hjl))
      · obtain ⟨j,hv,hw,hg⟩ := hcover h (not_le.mp he) hH
        refine Or.inr ⟨j,h,hv,hw,lt_of_le_of_lt ?_ (hbad.trans_le hp)⟩
        exact measure_mono (fun y hy i l hil => hg.trans (hy i l hil))
    · obtain ⟨j,hv,hw,hg⟩ := hgrowth
      refine Or.inr ⟨j,H,hv,hw,lt_of_le_of_lt ?_ (hbad.trans_le hp)⟩
      exact measure_mono (fun y hy i l hil => hg.trans (hy i l hil))
  exact (measure_mono hsub).trans ((measure_union_le E F).trans
    (by simpa only [add_assoc] using add_le_add hshort hF))

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

lemma noDropProduct_le_raw {d k : ℕ} (ℓ : Vector d) (ω : Environment d)
    (hω : ∀ x H, NoDrop ℓ x ≤ᵐ[quenchedKernel (ω,x)] Cross ℓ x H)
    (x : Fin k → Lattice d) (H : ℕ) :
    ENNReal.ofReal (noDropProduct ℓ x ω) ≤ rawTupleEndpointLaw ℓ H ω x Set.univ := by
  rw [noDropProduct,ENNReal.ofReal_prod_of_nonneg (fun j _ => ENNReal.toReal_nonneg),
    rawTupleEndpointLaw,Measure.pi_univ]
  apply Finset.prod_le_prod
  intro j _
  rw [ENNReal.ofReal_toReal (show noDropQuenched ℓ (x j) ω ≠ ⊤ from measure_ne_top _ _)]
  have hh : noDropQuenched ℓ (x j) ω ≤ crossingQuenched ℓ (x j) H ω :=
    measure_mono_ae (hω (x j) H)
  rw [crossingQuenched_eq_hitKernel] at hh
  exact hh

lemma fullStream_noDrop_lower {d k : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ ω ∂environmentLaw ν, ∀ (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π],
      ∀ H : ℕ, ENNReal.ofReal (∫ x, noDropProduct ℓ x ω ∂π) ≤
        rawTupleMixture ℓ H π ω Set.univ := by
  filter_upwards [quenched_noDrop_subset_cross_ae ν ℓ htrans] with ω hω π hπ H
  have hI : Integrable (fun x => noDropProduct ℓ x ω) π :=
    integrable_of_nonneg_bound π (measurable_of_countable _) (fun x => noDropProduct_bounds ℓ x ω)
  rw [ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall
    (fun x => (noDropProduct_bounds ℓ x ω).1)),rawTupleMixture_apply]
  exact lintegral_mono fun x => noDropProduct_le_raw ℓ ω hω x H

theorem fullStream_small_mass_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (ℓ : Vector d)
    (hℓ : dot ℓ ℓ = 1) (htrans : DirectionallyTransient ν ℓ) (e : Fin d) :
    ∃ lam C : ℝ, 0 < lam ∧ lam ≤ 1 ∧ 0 < C ∧
      ∀ Bstar : ℝ, 0 < Bstar → ∀ k : ℕ, 1 ≤ k → ∃ G : ℕ,
      ∀ (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π],
        (∀ᵐ x ∂π, Pairwise fun i j => (G:ℤ) ≤ |x i e-x j e|) →
        ∀ s : ℝ, Real.exp (-Bstar) ≤ s →
        environmentLaw ν {ω | ∃ H : ℕ, rawTupleMixture ℓ H π ω Set.univ < ENNReal.ofReal s} ≤
          ENNReal.ofReal (Real.exp (C*k)*s^lam) := by
  obtain ⟨lam,C,hlam,hlam1,hC,hb⟩ := separated_initial_inverse_moment ν hue ℓ hℓ htrans e
  refine ⟨lam,C,hlam,hlam1,hC,fun Bstar hB k hk => ?_⟩
  obtain ⟨G,hG⟩ := hb Bstar hB k hk
  refine ⟨G,fun π hπ hsep s hs => ?_⟩
  apply le_trans _ (hG π hsep s hs)
  apply measure_mono_ae
  filter_upwards [fullStream_noDrop_lower ν ℓ htrans] with ω hω
  rintro ⟨H,hH⟩
  have hq := (hω π H).trans_lt hH
  have hs0 : 0 < s := (Real.exp_pos _).trans_le hs
  have hqs : (∫ x, noDropProduct ℓ x ω ∂π) < s := (ENNReal.ofReal_lt_ofReal_iff hs0).mp hq
  change (∫ x, noDropProduct ℓ x ω ∂π) < 2*s
  linarith

end DirectionalTransience

end

end OAI
