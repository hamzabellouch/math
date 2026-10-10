import Mathlib
import OAI.Probability.SKBarriers.Replicas.ReplicaMarginal
import OAI.Probability.SKBarriers.Replicas.PairGibbsGap
import OAI.Probability.SKBarriers.Replicas.ReplicaEventSplit
import OAI.Probability.SKBarriers.Locking.NarrowScaledGap
import OAI.Probability.SKBarriers.Locking.NarrowCDFMass

namespace OAI

section

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def narrowLockingSet (n : ℕ) (μ : ProbabilityMeasure ℝ) (t₀ ρ : ℝ) : Finset (ReplicaConfig n 3) := by
  classical
  exact Finset.univ.filter (fun s => tripleR s∈Ioo (t₀/2) (3*t₀) ∧
    (μ : Measure ℝ).real (Icc (tripleR s-ρ^8) (tripleR s+ρ^8))≤ρ^4 ∧
    tripleR s+ρ≤tripleQ s ∧ ρ^20≤|tripleDelta s| ∧ |tripleDelta s|≤2*ρ^20)

theorem narrowLocking_pressure_gap {β t₀ : ℝ} (hβ : β≠0)
    (ht₀ : 0<t₀) (ht₁ : 3*t₀<1) (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β)
    (h0 : (0:ℝ)∈(μ : Measure ℝ).support)
    (hS : ∀ q∈Icc (0:ℝ) 1,scalarCDFSusceptibilityAverage β (cdf (μ : Measure ℝ)) q=
      (∫ x in q..1,cdf (μ : Measure ℝ) x)+cdf (μ : Measure ℝ) q*(q-scalarCDFOverlap β (cdf (μ : Measure ℝ)) q))
    (hΓ : ∀ r∈Ioo (t₀/2) (3*t₀),scalarCDFOverlap β (cdf (μ : Measure ℝ)) r=r) :
    ∃ ρ₀ c : ℝ,0<ρ₀ ∧ 0<c ∧ ∀ (n : ℕ),0<n → ∀ ρ : ℝ,0<ρ → ρ≤ρ₀ →
      ∀ s∈narrowLockingSet n μ t₀ ρ,
        |tripleQ s-scalarCDFOverlap β (cdf (μ : Measure ℝ)) (tripleQ s)|≤ρ^13 →
        matrixConstrainedPressure n 3 β (replicaGram s)≤3*finiteParisiInf β-c*ρ^43 := by
  let α := cdf (μ : Measure ℝ)
  have hα (z) : α z∈Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  have hm : 0<α (t₀/2) := cdf_pos_of_zero_mem_support μ h0 (half_pos ht₀)
  obtain ⟨r₀,c,hr₀,hc,H⟩ := narrowConstrainedPressure_scaled_gap hβ hm
  refine ⟨min r₀ (min 1 (t₀/2)),c,lt_min hr₀ (lt_min zero_lt_one (half_pos ht₀)),hc,?_⟩
  intro n hn ρ hρ hρ₀ s hs hdev
  obtain ⟨hr,hmass,hrq,hδ,hδ'⟩ := (Finset.mem_filter.mp hs).2
  have hρ1 : ρ≤1 := (le_min_iff.mp (le_min_iff.mp hρ₀).2).1
  have hρt : ρ≤t₀/2 := (le_min_iff.mp (le_min_iff.mp hρ₀).2).2
  have hpow : ρ^8≤ρ := pow_le_of_le_one hρ.le hρ1 (by decide)
  have hq₁ : tripleQ s≤1 := (abs_le.mp (abs_overlap_le_one (s 1) (s 2))).2
  have hq₀ : 0≤tripleQ s := by linarith only [hr.1,hrq,hρ,ht₀]
  let u := (tripleR s+3*t₀)/2
  have hru : tripleR s<u := by dsimp only [u]; linarith only [hr.2]
  have hu : u<3*t₀ := by dsimp only [u]; linarith only [hr.2]
  have HG := H α hα (supported_probability_cdf_one μ hμ) n hn ρ (tripleR s) (tripleQ s) u (tripleDelta s)
    hρ (le_min_iff.mp hρ₀).1 (hpow.trans (hρt.trans hr.1.le)) hrq hq₁ hru (hu.le.trans ht₁.le)
    (fun x hx => hΓ x ⟨hr.1.trans_le hx.1,hx.2.trans_lt hu⟩)
    (α.mono hr.1.le) (hS _ ⟨hq₀,hq₁⟩) hdev
    ((cdf_sub_le_real_Icc μ (by linarith only [pow_nonneg hρ.le 8])).trans hmass) hδ'
    (by rw [← replicaGram_triple_overlap hn]; exact replicaGram_feasible s)
  rw [hmin,← replicaGram_triple_overlap hn] at HG
  have HD := pow_le_pow_left₀ (pow_nonneg hρ.le 20) hδ 2
  rw [sq_abs] at HD
  have HC := mul_le_mul_of_nonneg_left HD (show 0≤c*ρ^3 by positivity)
  have HE : c*ρ^3*(ρ^20)^2=c*ρ^43 := by ring
  rw [HE] at HC
  linarith only [HG,HC]

theorem narrow_annulus_locking {β t₀ : ℝ} (hβ : 0<β)
    (ht₀ : 0<t₀) (ht₁ : 3*t₀<1) (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β)
    (h0 : (0:ℝ)∈(μ : Measure ℝ).support)
    (hS : ∀ q∈Icc (0:ℝ) 1,scalarCDFSusceptibilityAverage β (cdf (μ : Measure ℝ)) q=
      (∫ x in q..1,cdf (μ : Measure ℝ) x)+cdf (μ : Measure ℝ) q*(q-scalarCDFOverlap β (cdf (μ : Measure ℝ)) q))
    (hΓ : ∀ r∈Ioo (t₀/2) (3*t₀),scalarCDFOverlap β (cdf (μ : Measure ℝ)) r=r) :
    ∀ᶠ n : ℕ in atTop,
      (∫ J,replicaGibbsMass β J (narrowLockingSet n μ t₀ ((n:ℝ)^(-kappa))) ∂disorderLaw n)≤
        Real.exp (-(n:ℝ)^((4:ℝ)/5)) := by
  classical
  let α := cdf (μ : Measure ℝ)
  have hα (z) : α z∈Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  obtain ⟨ρ₀,c,hρ₀,hc,Hgap⟩ := narrowLocking_pressure_gap hβ.ne' ht₀ ht₁ μ hμ hmin h0 hS hΓ
  have HP := eventual_pairMismatch_polynomial_bound (A:=1) (a:=13*kappa) (t:=(4:ℝ)/5) (ε:=1/2)
    hβ zero_lt_one (by norm_num [kappa]) (by norm_num [kappa]) (by norm_num [kappa]) (by norm_num)
    α hα (supported_probability_cdf_one μ hμ) hmin
  have HT := eventual_replicaGibbsMass_polynomial_gap (c:=c) (a:=43*kappa) (t:=(4:ℝ)/5) (ε:=1/4)
    hβ 3 3 (by decide) hc (by norm_num [kappa]) (by norm_num [kappa]) (by norm_num [kappa]) (by norm_num)
  have Hρ := (tendsto_rpow_neg_atTop (by norm_num [kappa] : 0<kappa)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [HP,HT,Hρ.eventually_le_const hρ₀,eventually_gt_atTop (0:ℕ)] with n hnP hnT hρn hn0
  have hp : (0:ℝ)<n := by exact_mod_cast hn0
  let ρ := (n:ℝ)^(-kappa)
  have hρ : 0<ρ := Real.rpow_pos_of_pos hp _
  have Hpow (k : ℕ) : ρ^k=(n:ℝ)^(-((k:ℝ)*kappa)) := by
    rw [← Real.rpow_natCast ρ k,← Real.rpow_mul hp.le]
    congr 1
    ring
  let S := narrowLockingSet n μ t₀ ρ
  let T := S.filter (fun s => |tripleQ s-scalarCDFOverlap β α (tripleQ s)|≤ρ^13)
  have HT' : (∫ J,replicaGibbsMass β J T ∂disorderLaw n)≤(1/4)*Real.exp (-(n:ℝ)^((4:ℝ)/5)) := by
    apply hnT (Fin 3 → Fin (n+1)) (by simp) tripleReplicaCode (fun s t H => tripleReplicaCode_gram hn0 H)
    intro s hs
    have HH := Finset.mem_filter.mp hs
    have HG := Hgap n hn0 ρ hρ hρn s HH.1 HH.2
    simpa only [Hpow 43,Nat.cast_ofNat] using HG
  have Hsplit := replicaGibbsMass_integral_or_or_flip (0:Fin 3) β S T
    (Finset.univ.filter (fun s : ReplicaConfig n 3 => Fin.tail s∈pairMismatchSet n β α (ρ^13)))
    (fun s hs => by
      by_cases hg : |tripleQ s-scalarCDFOverlap β α (tripleQ s)|≤ρ^13
      · exact Or.inl (Finset.mem_filter.mpr ⟨hs,hg⟩)
      · right; right
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,(not_le.mp hg).le⟩⟩
        obtain ⟨hr,hm,hrq,hd⟩ := (Finset.mem_filter.mp hs).2
        change 0≤tripleQ s
        linarith only [hr.1,hrq,hρ,ht₀])
  simp_rw [replicaGibbsMass_tail,Hpow 13] at Hsplit
  norm_num only [Nat.cast_ofNat,one_mul] at Hsplit hnP
  linarith only [Hsplit,HT',hnP]

end SK.Analytic

end
end

end OAI
