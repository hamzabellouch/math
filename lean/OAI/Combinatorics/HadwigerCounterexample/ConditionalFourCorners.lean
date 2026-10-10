import OAI.Combinatorics.HadwigerCounterexample.UnseenCrossingFactorization
import OAI.Combinatorics.HadwigerCounterexample.GramConditionedLaws

namespace OAI

/-! # Conditional Four Corners -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I J : Type} [Fintype I] [DecidableEq I]
set_option maxHeartbeats 600000 in
private theorem stip_mask (E : Rail I) (t : Vec E) (p : Wgt (Rack I N)) (δ : ℝ)
    (hδ : 0≤δ) (hh : |avg unif p|≤δ) (h : ∀ f:Vec E,f≠0 →
      |avg unif (fun i=>phasedBy (ledgerM E f) i*p i)|≤bp (-(N:ℝ)/2)) :
    |partMean (fun x=>traced x E t) p|≤δ+bp (-(N:ℝ)/2) := by
  classical
  have he (f : Vec E) :
      |vectorPhase f t*avg unif (fun i : Rack I N=>phasedBy (ledgerM E f) i*p i)|≤ δ+bp (-(N:ℝ)/2) := by
    rw [abs_mul,vectorPhase,wsign_abs,one_mul]
    by_cases hz : f=0
    · subst f; simpa only [ledger_zero,layer_zero,one_mul] using hh.trans (le_add_of_nonneg_right (bp_pos (-(N:ℝ)/2)).le)
    exact (h f hz).trans (le_add_of_nonneg_left hδ)
  have hf : partMean (fun x=>traced x E t) p=avg unif (fun f:Vec E => vectorPhase f t*avg unif
      (fun i:Rack I N=>phasedBy (ledgerM E f) i*p i)) := by
    unfold partMean; simp_rw [rail_expand,←avg_mul]
    rw [avg_avg]; simp_rw [←avg_mul']; exact avg_congr (fun i _=>avg_congr fun j _=>by ring)
  rw [hf]
  exact (abs_avg_le unif_law.nz).trans (unif_law.avg_le he)
namespace Template
variable (v : Template p I)

theorem pack_bound (v : Template p I) (j : I) (U : Wgt (Keys (p:=p) v.t N))
    (hU : ∀ i, |U i|≤1) (i) : |packSecs v j U i| ≤1 := by
  unfold packSecs; rw [Finset.abs_prod]
  exact (Finset.prod_le_prod₀ (fun i _=>abs_nonneg _) (fun i _ => hU _)).trans_eq (by simp)

set_option maxHeartbeats 800000 in
theorem lopsided (v : Template p I) (j : I) (q : I→F)
    (U : Wgt (Keys (p:=p) v.t N)) (δ : ℝ) (hδ : 0≤δ)
    (hU : ∀ x,|U x|≤1) (h : chairCut v j U δ)
    (hW : carried U (ownPart (p:=p) v.t q))
    (Z : GeoM v.seam) :
    |partMean (gramPart Z) (packSecs v j U)|≤δ+bp (-(N:ℝ)/2) := by
  classical
  let P := packSecs v j U
  let Q := gramPart Z (N:=N)
  have hb := bp_pos (-(N:ℝ)/2)
  by_cases hp : ∃ x,Q x∧P x≠0
  · obtain ⟨x,hx,hP⟩ := hp
    let E := cantRail v j
    let T (y : v.PackStack N) := traced y E (cantVec v j Z)
    have hg i : ind (Q i)*P i=ind (T i)*P i := by
      by_cases hh : P i=0
      · rw [hh,mul_zero,mul_zero]
      rw [show Q i=T i from propext
        (cant_bridge v j q Z x i (pack_gate v j q U hW hP) (pack_gate v j q U hW hh) hx)]
    change |avg unif (fun x => ind (Q x)*P x)|≤_
    simp_rw [hg]
    exact stip_mask E (cantVec v j Z) P δ hδ (global_quart v j U hU δ h) (cant_leak v j U hU)
  have hh (x) : ind (Q x)*P x=0 := by
    by_cases he : Q x <;> simp only [he,ind_true,ind_false,one_mul,zero_mul]
    exact not_ne_iff.mp (fun hx => hp ⟨x,he,hx⟩)
  change |avg unif (fun x=>ind (Q x)*P x)|≤_
  simp_rw [hh,avg_zero,abs_zero]
  exact add_nonneg hδ hb.le

set_option maxHeartbeats 800000 in
theorem pack_hot (v : Template p I) (j : I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N))
    (δ : ℝ) (hδ : 0≤δ) (hU : ∀ x, |U x|≤1) (h : chairCut v j U δ)
    (hW : carried U (ownPart (p:=p) v.t q))
    (Z : GeoM v.seam) (k : ℝ) (hk : ∀ i,num (Port v.seam i)≤ k)
    (hN : 2*k-(N:ℝ) ≤ -1) :
    let W := netFact v.seam
    |avg (rackStation Z N) (packSecs v j U)|≤
      2*W*(num (Ports p)*(2*bp (k-N)))+W*(δ+bp (-(N:ℝ)/2)) := by
  classical
  intro W
  let B := pr unif (gramPart Z (N:=N))
  have hb := wave_norm Z N (fun i => by linarith only [hN,hk i])
  have h0 : 0<W := netFact_pos
  have he : 0<B := (inv_pos_of_pos h0).trans_le hb
  let V := packSecs v j U
  let D := avg (rackWave Z N) V
  have hl := lopsided v j q U δ hδ hU h hW Z
  rw [part_reset _ _ he,abs_mul,abs_of_nonneg he.le] at hl
  have hh :
      |D| ≤ W*(δ+bp (-(N:ℝ)/2)) := by
    apply le_of_mul_le_mul_left _ (inv_pos_of_pos h0)
    exact (le_trans (mul_le_mul_of_nonneg_right hb (abs_nonneg _)) hl).trans_eq (by field_simp)
  let A := avg (rackStation Z N) V
  have hs := compare_station Z V (pack_bound v j U hU) k hk hN
  change |A|≤_
  exact le_trans (by simpa only [sub_zero] using (abs_sub_le A D 0)) (add_le_add hs hh)
end Template
end HadwigerCounterexample

end

end OAI
