import Mathlib
import OAI.MathematicalPhysics.BFSS.OscillatorLimits

namespace OAI

/-! Strong core and closed energy extraction with lower limits. -/

namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2

structure NormalCoreEnergyData (h : ℕ → ℝ) (f : ℕ → G.invariantCore) (L : ℝ) where
  S : Finset (Boson N)
  zero : ∀ q ∈ S, q ∈ M.massiveZeros
  cover : M.massiveZeros = ⋃ q ∈ S, M.gaugeOrbit q
  orbitDisjoint : Pairwise (fun i j : S => Disjoint (M.gaugeOrbit i.val) (M.gaugeOrbit j.val))
  P : (q : S) → G.MeasuredNormalPatch q.val
  patchDisjoint : Pairwise (fun i j : S => Disjoint (Function.support (P i).cutoff) (Function.support (P j).cutoff))
  u : (q : S) → Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q.val))
  v : (q : S) → M.NormalGradient q.val
  σ : ℕ → ℕ
  mono : StrictMono σ
  equivariant : ∀ q : S, u q ∈ G.normalEquivariantSpace q.val
  domain : ∀ q : S, M.NormalFormDomain q.val (u q) (v q)
  profiles : ∀ q : S, Tendsto (fun n => (P q).profile (h (σ n)) (f (σ n))) atTop (𝓝 (u q))
  norm : Tendsto (fun n => ‖coreToL2 (f (σ n)).val‖^2) atTop (𝓝 (∑ q : S, ‖u q‖^2))
  energy : (∑ q : S, M.normalOscillatorForm q.val (u q) (v q)) ≤ L

def NormalCoreEnergyConclusion (h : ℕ → ℝ) (f : ℕ → G.invariantCore) (L : ℝ) : Prop :=
  Nonempty (G.NormalCoreEnergyData h f L)

theorem normalCore_energy_extraction (hN : 2 ≤ N)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n ∧ h n ≤ 1) (hzero : Tendsto h atTop (𝓝 0))
    (f : ℕ → G.invariantCore) (E : ℝ≥0)
    (hnorm : ∀ n, ‖coreToL2 (f n).val‖^2 ≤ E)
    (henergy : ∀ n, M.deformedCoreEnergy (h n) 1 (f n).val ≤ E)
    (L : ℝ) (hL : Tendsto (fun n => M.deformedCoreEnergy (h n) 1 (f n).val) atTop (𝓝 L)) :
    G.NormalCoreEnergyConclusion h f L := by
  classical
  unfold NormalCoreEnergyConclusion
  obtain ⟨S,hS,hcov,hdis,P,hPd,δ,c,K,hδ,hc,hK,hbound⟩ := G.normalPatch_norm_exhaustion hN
  let C : ℝ := ((E : ℝ)+K*E)/(c/2*δ^2)
  have hden : 0 < c/2*δ^2 := mul_pos (half_pos hc) (sq_pos_of_pos hδ)
  let r : ℕ → ℝ := fun n => ‖coreToL2 (f n).val‖^2 - ∑ q : S, ‖(P q).profile (h n) (f n)‖^2
  have hr (n : ℕ) : 0 ≤ r n ∧ r n ≤ (h n)^2*C := by
    have hb := hbound (h n) (hh n).1 (hh n).2 (f n)
    simp_rw [←MeasuredNormalPatch.profile_norm_square] at hb
    refine ⟨hb.1,?_⟩
    change r n ≤ (h n)^2 * (((E : ℝ)+K*E)/(c/2*δ^2))
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hden).2
    have he : M.deformedCoreEnergy (h n) 1 (f n).val + K*‖coreToL2 (f n).val‖^2 ≤ (E : ℝ)+K*E :=
      add_le_add (henergy n) (mul_le_mul_of_nonneg_left (hnorm n) hK)
    have hs := hb.2.trans (mul_le_mul_of_nonneg_left he (sq_nonneg _))
    change r n * (c/2*δ^2) ≤ _
    rw [mul_comm (r n)]
    exact hs
  have hrzero : Tendsto r atTop (nhds 0) :=
    squeeze_zero (fun n => (hr n).1) (fun n => (hr n).2)
      (by simpa using (hzero.pow 2).mul_const C)
  let X (q : S) := Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q.val))
  let a : ℕ → ((q : S) → X q) := fun n q => (P q).profile (h n) (f n)
  have hcompact (q : S) : IsCompact (closure (range (fun n => a n q))) :=
    ((P q).profile_totallyBounded hN h hh hzero f E hnorm henergy).closure.isCompact_of_isClosed isClosed_closure
  have hprod := isCompact_pi_infinite hcompact
  obtain ⟨v,hv,σ,hσ,ht⟩ := hprod.tendsto_subseq (fun n q => subset_closure (mem_range_self n))
  have hcoord (q : S) : Tendsto (fun n => (P q).profile (h (σ n)) (f (σ n))) atTop (nhds (v q)) :=
    (tendsto_pi_nhds.mp ht) q
  have hsum : Tendsto (fun n => ∑ q : S, ‖(P q).profile (h (σ n)) (f (σ n))‖^2) atTop
      (nhds (∑ q : S, ‖v q‖^2)) := tendsto_finsetSum _ (fun q _ => (hcoord q).norm.pow 2)
  have hgrad := G.normalPatch_summed_energy_limit (fun q : S => q.val) P hN
    (fun q => hS q.val q.prop) hPd (fun n => h (σ n)) (fun n => hh (σ n))
    (hzero.comp hσ.tendsto_atTop) (fun n => f (σ n)) E
    (fun n => hnorm (σ n)) (fun n => henergy (σ n)) v hcoord
    (hrzero.comp hσ.tendsto_atTop) L (hL.comp hσ.tendsto_atTop)
  obtain ⟨w,hw,hwe⟩ := hgrad
  refine ⟨⟨S,hS,hcov,hdis,P,hPd,v,w,σ,hσ,?_,hw,hcoord,?_,hwe⟩⟩
  · intro q
    exact (G.normalEquivariantSpace_closed q.val).mem_of_tendsto (hcoord q)
      (Filter.Eventually.of_forall fun n => (P q).profile_mem_equivariantSpace _ _)
  · have ht' := (hrzero.comp hσ.tendsto_atTop).add hsum
    simpa only [Function.comp_apply,r,zero_add,sub_add_cancel] using ht'
end
end BFSSQuantum.AlgebraData.GaugeData
namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2
  MeasuredNormalPatch.closedProfile

structure NormalClosedEnergyData (h : ℕ → ℝ) (x : ℕ → G.coreNormClosure) (L : ℝ) where
  S : Finset (Boson N)
  zero : ∀ q ∈ S, q ∈ M.massiveZeros
  cover : M.massiveZeros = ⋃ q ∈ S, M.gaugeOrbit q
  orbitDisjoint : Pairwise (fun i j : S => Disjoint (M.gaugeOrbit i.val) (M.gaugeOrbit j.val))
  P : (q : S) → G.MeasuredNormalPatch q.val
  patchDisjoint : Pairwise (fun i j : S => Disjoint (Function.support (P i).cutoff) (Function.support (P j).cutoff))
  u : (q : S) → Lp (Fermion N) 2 (volume : Measure (M.NormalCoordinates q.val))
  v : (q : S) → M.NormalGradient q.val
  σ : ℕ → ℕ
  mono : StrictMono σ
  equivariant : ∀ q : S, u q ∈ G.normalEquivariantSpace q.val
  domain : ∀ q : S, M.NormalFormDomain q.val (u q) (v q)
  profiles : ∀ q : S, Tendsto (fun n => (P q).closedProfile (h (σ n)) (x (σ n))) atTop (𝓝 (u q))
  norm : Tendsto (fun n => ‖x (σ n)‖^2) atTop (𝓝 (∑ q : S, ‖u q‖^2))
  energy : (∑ q : S, M.normalOscillatorForm q.val (u q) (v q)) ≤ L

def NormalClosedEnergyConclusion (h : ℕ → ℝ) (x : ℕ → G.coreNormClosure) (L : ℝ) : Prop :=
  Nonempty (G.NormalClosedEnergyData h x L)

theorem normalClosed_energy_extraction (hN : 2 ≤ N)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n ∧ h n ≤ 1) (hzero : Tendsto h atTop (𝓝 0))
    (x : ℕ → G.coreNormClosure) (y : ℕ → SpinIndex → FullL2 N) (B : ℝ≥0)
    (hg : ∀ n, ((x n : FullL2 N),y n) ∈ G.deformedModelGraph (h n) 1)
    (hx : ∀ n, ‖x n‖ ≤ B) (hy : ∀ n α, ‖y n α‖ ≤ B)
    (L : ℝ) (hL : Tendsto (fun n => jointEnergy (y n)) atTop (𝓝 L)) :
    G.NormalClosedEnergyConclusion h x L := by
  classical
  unfold NormalClosedEnergyConclusion
  let ε : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := one_div_pos.mpr (by positivity)
  have hε1 (n : ℕ) : ε n ≤ 1 := by
    apply (div_le_iff₀ (show 0 < (n : ℝ)+1 by positivity)).2
    simp only [one_mul]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hεzero : Tendsto ε atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose f hf hQ using (fun n => G.deformedModelGraph_approx (h n) 1 (hg n) (ε n) (hε n))
  let C : ℝ≥0 := B+1
  have hcf (n : ℕ) : ‖coreToL2 (f n).val‖ ≤ C := by
    have hd : dist (coreToL2 (f n).val) (x n : FullL2 N) ≤ 1 :=
      by rw [dist_comm]; exact (hf n).le.trans (hε1 n)
    have ha := norm_le_norm_add_const_of_dist_le hd
    change _ ≤ (B : ℝ)+1
    exact ha.trans (add_le_add (show ‖(x n : FullL2 N)‖ ≤ B from hx n) le_rfl)
  have hqf (n : ℕ) (α : SpinIndex) : ‖coreToL2 (M.deformedCoreCharge (h n) 1 α (f n).val)‖ ≤ C := by
    have hd : dist (coreToL2 (M.deformedCoreCharge (h n) 1 α (f n).val)) (y n α) ≤ 1 :=
      by rw [dist_comm]; exact (hQ n α).le.trans (hε1 n)
    have ha := norm_le_norm_add_const_of_dist_le hd
    change _ ≤ (B : ℝ)+1
    linarith [hy n α]
  have hfs (n : ℕ) : ‖coreToL2 (f n).val‖^2 ≤ (C^2 : ℝ≥0) :=
    pow_le_pow_left₀ (norm_nonneg _) (hcf n) 2
  have he (n : ℕ) : M.deformedCoreEnergy (h n) 1 (f n).val ≤ (C^2 : ℝ≥0) := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun α _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hqf n α) 2)
    unfold AlgebraData.deformedCoreEnergy
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    norm_num only [Nat.cast_ofNat] at hs
    change _ ≤ (C : ℝ)^2
    linarith
  have henergyDist : Tendsto (fun n => dist (jointEnergy (y n))
      (M.deformedCoreEnergy (h n) 1 (f n).val)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => dist_nonneg) (g := fun n => ε n*(2*(C : ℝ))) _
      (by simpa only [zero_mul] using hεzero.mul_const (2*(C : ℝ)))
    intro n
    exact jointEnergy_distance_le (y n) (M.deformedChargeVector (h n) 1 (f n).val)
      (hε n).le (fun α => (hy n α).trans (by change (B : ℝ) ≤ (B : ℝ)+1; linarith))
      (hqf n) (fun α => (hQ n α).le)
  have hdata := G.normalCore_energy_extraction hN h hh hzero f (C^2) hfs he L
    (hL.congr_dist henergyDist)
  unfold NormalCoreEnergyConclusion at hdata
  obtain ⟨⟨S,hS,hcov,hdis,P,hPd,v,w,σ,hσ,hve,hw,hcoord,hnorm,hlim⟩⟩ := hdata
  have hdist (q : S) : Tendsto (fun n => dist ((P q).profile (h n) (f n))
      ((P q).closedProfile (h n) (x n))) atTop (nhds 0) := by
    apply squeeze_zero (fun n => dist_nonneg) _ hεzero
    intro n
    exact ((P q).closedProfile_core_dist_le (hh n).1 (hh n).2 (f n) (x n)).trans
      (by rw [dist_comm]; exact (hf n).le)
  refine ⟨⟨S,hS,hcov,hdis,P,hPd,v,w,σ,hσ,hve,hw,
    fun q => (hcoord q).congr_dist ((hdist q).comp hσ.tendsto_atTop),?_,hlim⟩⟩
  have hnormdist : Tendsto (fun n => dist (‖coreToL2 (f n).val‖^2) (‖x n‖^2)) atTop (nhds 0) := by
    apply squeeze_zero (fun n => dist_nonneg)
      (g := fun n => ε n*((C : ℝ)+B)) _ (by simpa only [zero_mul] using hεzero.mul_const ((C : ℝ)+B))
    intro n
    have hd := BFSSRellich.normSquare_distance_le (coreToL2 (f n).val) (x n : FullL2 N)
    apply hd.trans
    apply mul_le_mul
    · rw [dist_comm]; exact (hf n).le
    · exact add_le_add (hcf n) (hx n)
    · exact add_nonneg (norm_nonneg _) (norm_nonneg _)
    · exact (hε n).le
  exact hnorm.congr_dist (hnormdist.comp hσ.tendsto_atTop)
end
end BFSSQuantum.AlgebraData.GaugeData
namespace BFSSNormalAnalysis
noncomputable section
open Set Filter Topology

lemma nonnegative_bounded_liminf_subsequence (a : ℕ → ℝ) (C : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, a n ≤ C) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ Tendsto (a ∘ τ) atTop (𝓝 (liminf a atTop)) := by
  have hlow : IsBoundedUnder (· ≥ ·) atTop a := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ a n
    exact Eventually.of_forall ha
  have hupp : IsBoundedUnder (· ≤ ·) atTop a := by
    refine ⟨C, ?_⟩
    change ∀ᶠ n in atTop, a n ≤ C
    exact Eventually.of_forall hb
  obtain ⟨t, ht, htTop⟩ := exists_seq_tendsto_liminf hupp.isCoboundedUnder_flip hlow
  obtain ⟨s, hs, hts⟩ := strictMono_subseq_of_tendsto_atTop htTop
  exact ⟨t ∘ s, hts, ht.comp hs.tendsto_atTop⟩
end
end BFSSNormalAnalysis

namespace BFSSQuantum
noncomputable section
open Set Filter Topology Finset
open scoped NNReal
variable {N : ℕ}

lemma charge_norm_bound_of_energy (y : SpinIndex → FullL2 N) (E : ℝ≥0)
    (he : jointEnergy y ≤ E) (α : SpinIndex) : ‖y α‖ ≤ 16*(E : ℝ)+1 := by
  have hs : ‖y α‖^2 ≤ ∑ β : SpinIndex, ‖y β‖^2 :=
    Finset.single_le_sum (fun β _ => sq_nonneg ‖y β‖) (Finset.mem_univ α)
  unfold jointEnergy at he
  have hy := norm_nonneg (y α)
  have hE : (0 : ℝ) ≤ E := E.coe_nonneg
  nlinarith [sq_nonneg (‖y α‖-1)]
end
end BFSSQuantum

namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2
  MeasuredNormalPatch.closedProfile

def NormalClosedEnergyData.reindex {h : ℕ → ℝ} {x : ℕ → G.coreNormClosure} {L : ℝ}
    {τ : ℕ → ℕ} (D : G.NormalClosedEnergyData (h ∘ τ) (x ∘ τ) L) (hτ : StrictMono τ) :
    G.NormalClosedEnergyData h x L where
  S := D.S
  zero := D.zero
  cover := D.cover
  orbitDisjoint := D.orbitDisjoint
  P := D.P
  patchDisjoint := D.patchDisjoint
  u := D.u
  v := D.v
  σ := τ ∘ D.σ
  mono := hτ.comp D.mono
  equivariant := D.equivariant
  domain := D.domain
  profiles := D.profiles
  norm := D.norm
  energy := D.energy

theorem normalClosed_liminf_extraction (hN : 2 ≤ N)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n ∧ h n ≤ 1) (hzero : Tendsto h atTop (𝓝 0))
    (x : ℕ → G.coreNormClosure) (y : ℕ → SpinIndex → FullL2 N) (A E : ℝ≥0)
    (hg : ∀ n, ((x n : FullL2 N),y n) ∈ G.deformedModelGraph (h n) 1)
    (hx : ∀ n, ‖x n‖ ≤ A) (he : ∀ n, jointEnergy (y n) ≤ E) :
    G.NormalClosedEnergyConclusion h x (liminf (fun n => jointEnergy (y n)) atTop) := by
  obtain ⟨τ,hτ,ht⟩ := BFSSNormalAnalysis.nonnegative_bounded_liminf_subsequence
    (fun n => jointEnergy (y n)) E (fun n => jointEnergy_nonneg _) he
  let B : ℝ≥0 := A+16*E+1
  have hBx (n : ℕ) : ‖x n‖ ≤ B := by
    change ‖x n‖ ≤ (A : ℝ)+16*(E : ℝ)+1
    linarith [hx n,E.coe_nonneg]
  have hBy (n : ℕ) (α : SpinIndex) : ‖y n α‖ ≤ B := by
    change ‖y n α‖ ≤ (A : ℝ)+16*(E : ℝ)+1
    linarith [charge_norm_bound_of_energy (y n) E (he n) α,A.coe_nonneg]
  have hd := G.normalClosed_energy_extraction hN (h ∘ τ) (fun n => hh (τ n))
    (hzero.comp hτ.tendsto_atTop) (x ∘ τ) (y ∘ τ) B (fun n => hg (τ n))
    (fun n => hBx (τ n)) (fun n α => hBy (τ n) α) _ ht
  obtain ⟨D⟩ := hd
  exact ⟨D.reindex G hτ⟩
end
end BFSSQuantum.AlgebraData.GaugeData

end OAI
