import OAI.Combinatorics.CycleDecomposition.LayerCosts

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {P : AssignedPiece V} {Dstar : ℝ}

def Layers.pieceSequence (H : Layers P Dstar) (j : ℕ) : ℝ :=
  if j < H.count then H.pieceMass j else 0

lemma Layers.pieceSequence_nonneg (H : Layers P Dstar) (j) : 0 ≤ H.pieceSequence j := by
  unfold Layers.pieceSequence
  split_ifs
  · exact vertexMass_nonneg _
  · rfl

lemma Layers.pieceSequence_zero (H : Layers P Dstar) (j) (hj : H.count ≤ j) :
    H.pieceSequence j = 0 := by simp only [Layers.pieceSequence,ite_eq_right (by omega : ¬ j < H.count)]

lemma Layers.past_mass_eq_sequence (H : Layers P Dstar) (k) (hk : k ≤ H.count) :
    vertexMass (pastPieces H.system 0 k [P]) = ∑ j ∈ range k, H.pieceSequence j := by
  rw [pastPieces_mass]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.zero_add,Layers.pieceSequence,ite_eq_left (by have := Finset.mem_range.mp hj; omega : j < H.count)]

lemma Layers.prefix_choice (H : Layers P Dstar) :
    vertexMass (pastPieces H.system 0 H.count [P]) = 0 ∨
    ∃ i < H.count, 0 < H.pieceMass i ∧
      ∀ k ≤ H.count, k ≤ i+201 →
        vertexMass (pastPieces H.system 0 k [P]) ≤ ErdosGallai.mainP*H.pieceMass i := by
  by_cases he : ∃ j, 0 < H.pieceSequence j
  · right
    obtain ⟨i,hi,hpref⟩ := ErdosGallai.prefix_selection H.pieceSequence H.pieceSequence_nonneg
      200 H.count H.pieceSequence_zero he
    have hic : i < H.count := by
      by_contra hi'
      rw [H.pieceSequence_zero i (by omega)] at hi
      linarith
    simp only [Layers.pieceSequence,ite_eq_left hic] at hi
    refine ⟨i,hic,hi,?_⟩
    intro k hk hki
    rw [H.past_mass_eq_sequence k hk]
    have hh : (∑ j ∈ range k, H.pieceSequence j) ≤ ∑ j ∈ range (i+200+1), H.pieceSequence j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun j _ _ => H.pieceSequence_nonneg j)
    apply hh.trans
    norm_num only [Layers.pieceSequence,ite_eq_left hic,ErdosGallai.mainP,Nat.cast_ofNat] at hpref ⊢
    exact hpref
  · left
    rw [H.past_mass_eq_sequence H.count le_rfl]
    apply Finset.sum_eq_zero
    intro j _
    exact le_antisymm (le_of_not_gt (fun h => he ⟨j,h⟩)) (H.pieceSequence_nonneg j)

end
end ErdosGallai.Scale

end

section

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable

lemma main_edge_bound {V : Type} [Fintype V] (G : SimpleGraph V) :
    2*(Scale.edgeCount G:ℝ) ≤ (Fintype.card V:ℝ)^2 := by
  classical
  have h : (G.edgeFinset.card:ℝ) ≤ ((Fintype.card V).choose 2:ℝ) :=
    Nat.cast_le.mpr G.card_edgeFinset_le_card_choose_two
  rw [Nat.cast_choose_two] at h
  change 2*(G.edgeFinset.card:ℝ) ≤ _
  nlinarith [(Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)]

lemma main_cost_eq_scale {V : Type} [Fintype V] (G : SimpleGraph V) :
    decompositionCost G = Scale.decompositionCost G := by rfl
lemma main_cost_eq_batch {V : Type} [Fintype V] (G : SimpleGraph V) :
    decompositionCost G = Batch.decompositionCost G := by rfl

theorem main_cost_bound : ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    (decompositionCost G:ℝ) ≤ C*Batch.inductionPhi (Fintype.card V)*Fintype.card V := by
  classical
  let wmin : ℝ := max 80 (((mainA₁+1)/Batch.inductionDelta)^2)
  obtain ⟨Da,ha,hLayers⟩ := Scale.uniform_layers
  obtain ⟨Db,hb,hPiece⟩ := Scale.uniform_committed_piece_cost
  obtain ⟨Dc,hc,hGap⟩ := Scale.uniform_gap_prefix_cost
  obtain ⟨Dr,hr,hReady⟩ := main_scale_ready_cutoff wmin
  let Dstar : ℝ := max (max Da Db) (max Dc Dr)
  have hDa : Da ≤ Dstar := (le_max_left Da Db).trans (le_max_left _ _)
  have hDb : Db ≤ Dstar := (le_max_right Da Db).trans (le_max_left _ _)
  have hDc : Dc ≤ Dstar := (le_max_left Dc Dr).trans (le_max_right _ _)
  have hDr : Dr ≤ Dstar := (le_max_right Dc Dr).trans (le_max_right _ _)
  have hDstar : 1 < Dstar := ha.trans_le hDa
  let C : ℝ := max (4*(20+Dstar+18*mainP)) (7*mainA₂)
  have hCbig : 4*(20+Dstar+18*mainP) ≤ C := le_max_left _ _
  have hCA : 7*mainA₂ ≤ C := le_max_right _ _
  have hCpos : 0 < C := lt_of_lt_of_le (by linarith [mainP_pos]) hCbig
  have hC : 0 ≤ C := hCpos.le
  refine ⟨C,hCpos,?_⟩
  have hmain : ∀ n : ℕ, ∀ (V : Type) [Fintype V], Fintype.card V = n → ∀ (G : SimpleGraph V),
      (decompositionCost G:ℝ) ≤ C*Batch.inductionPhi (Fintype.card V)*Fintype.card V := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ hn G
      subst n
      have hn0 : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      by_cases hsmall : (Fintype.card V:ℝ) < Dstar
      · have he := main_edge_bound G
        have hq : (decompositionCost G:ℝ) ≤ Scale.edgeCount G :=
          Nat.cast_le.mpr (Scale.decompositionCost_edgeCount G)
        have hnD := mul_le_mul_of_nonneg_right hsmall.le hn0
        have hphi := mul_le_mul_of_nonneg_left (Batch.inductionPhi_bounds (Fintype.card V)).1
          (mul_nonneg hC hn0)
        have hbig := mul_le_mul_of_nonneg_right hCbig hn0
        have hP := mul_nonneg mainP_pos.le hn0
        nlinarith only [he,hq,hnD,hphi,hbig,hP]
      · have hnD : Dstar ≤ (Fintype.card V:ℝ) := le_of_not_gt hsmall
        have hn1 : 1 < (Fintype.card V:ℝ) := hDstar.trans_le hnD
        let P : Scale.AssignedPiece V := ⟨univ,G,fun _ _ _ => ⟨mem_univ _,mem_univ _⟩⟩
        have hpc : P.vertices.card = Fintype.card V := Finset.card_univ
        have hp1 : 1 < (P.vertices.card:ℝ) := by simpa only [hpc] using hn1
        have hdeg : 2*(Scale.edgeCount P.graph:ℝ)/P.vertices.card ≤ P.vertices.card := by
          apply (div_le_iff₀ (by linarith : (0:ℝ) < P.vertices.card)).mpr
          simpa only [hpc,P,pow_two] using main_edge_bound G
        obtain ⟨H⟩ := hLayers Dstar hDa V P (by simpa only [hpc] using hnD) hdeg
        have hready' : ∀ j < H.count, MainScaleReady wmin (H.scale j) := by
          intro j hj
          exact hReady _ (hDr.trans (H.cutoff j hj))
        have hready : ∀ j < H.count, MainScaleReady 80 (H.scale j) := by
          intro j hj
          have hh := hready' j hj
          exact ⟨hh.gt_one,(le_max_left _ _).trans hh.log_large,hh.cycle_power,hh.batch_power,
            hh.bad_power,hh.skip_power,hh.active_eight⟩
        have ihw : ∀ (Q : Type) [Fintype Q] (F : SimpleGraph Q), Fintype.card Q < P.vertices.card →
            (decompositionCost F:ℝ) ≤ C*Fintype.card Q := by
          intro Q _ F hQ
          have hh := ih (Fintype.card Q) (by simpa only [hpc] using hQ) Q rfl F
          have hp := mul_le_mul_of_nonneg_left (Batch.inductionPhi_bounds (Fintype.card Q)).2
            (mul_nonneg hC (Nat.cast_nonneg (Fintype.card Q) : (0:ℝ) ≤ _))
          nlinarith only [hh,hp]
        have hpieces := hPiece Dstar hDb V P H C hC ihw
        have terminal (hm : Scale.vertexMass (Scale.pastPieces H.system 0 H.count [P]) ≤
            2*mainP*P.vertices.card) :
            (decompositionCost G:ℝ) ≤ C*Batch.inductionPhi (Fintype.card V)*Fintype.card V := by
          have hh := H.terminal_cost hp1 hready (9+C*mainEta) (hpieces H.count le_rfl)
          have ht := main_terminal_scalar _ P.vertices.card _ C Dstar (Nat.cast_nonneg _) hC hCbig hm hh
          simpa only [hpc,P,← main_cost_eq_scale] using ht
        rcases H.prefix_choice with hz | ⟨i,hic,hi,hprefix⟩
        · apply terminal
          rw [hz]
          exact mul_nonneg (mul_nonneg (by norm_num) mainP_pos.le) (Nat.cast_nonneg _)
        · by_cases hgap : i+200 < H.count
          · let t := C*Batch.inductionPhi ((H.scale i)^(3/10:ℝ))
            have ht : 0 ≤ t := mul_nonneg hC (by linarith [(Batch.inductionPhi_bounds ((H.scale i)^(3/10:ℝ))).1])
            have ihq : ∀ (Q : Type) [Fintype Q] (F : SimpleGraph Q), Fintype.card Q < P.vertices.card →
                (Fintype.card Q:ℝ) ≤ (H.scale i)^(3/10:ℝ) →
                (Batch.decompositionCost F:ℝ) ≤ t*Fintype.card Q := by
              intro Q _ F hQ hQD
              have hh := ih (Fintype.card Q) (by simpa only [hpc] using hQ) Q rfl F
              by_cases h0 : Fintype.card Q = 0
              · simpa only [h0,Nat.cast_zero,mul_zero,← main_cost_eq_batch] using hh
              · have h1 : (1:ℝ) ≤ Fintype.card Q := by exact_mod_cast (by omega : 1 ≤ Fintype.card Q)
                have hp := Batch.inductionPhi_monotone h1 (h1.trans hQD) hQD
                have hp' := mul_le_mul_of_nonneg_left hp
                  (mul_nonneg hC (Nat.cast_nonneg (Fintype.card Q) : (0:ℝ) ≤ _))
                change (decompositionCost F:ℝ) ≤ C*Batch.inductionPhi ((H.scale i)^(3/10:ℝ))*Fintype.card Q
                nlinarith only [hh,hp']
            have hlocal := hGap Dstar hDc V P H hp1 hready i hgap C t hC ht ihw ihq
              (hpieces (i+201) (by omega))
            have hscalar := main_gap_scalar _ P.vertices.card (H.pieceMass i)
              (Scale.vertexMass (Scale.pastPieces H.system 0 (i+201) [P]))
              ((Scale.pastCycles H.system 0 (i+201) [P]).length:ℝ)
              (H.mass (i+201)) (H.mass (i+1)) C t (logb 2 (H.scale i))
              (Nat.cast_nonneg _) (Scale.vertexMass_nonneg _) hC ht
              (by linarith [(hready i hic).log_large])
              (hprefix (i+201) (by omega) le_rfl) (H.gap_cycles hp1 hready i hgap)
              (H.gap_mass hp1 hready i hgap) (H.mass_lower (i+1))
              (H.mass_two hp1 (fun j hj => (hready j hj).log_large) (i+1) (by omega)) hlocal
            have habs := Batch.induction_cost_absorbed (H.scale i) P.vertices.card (H.pieceMass i)
              C mainA₁ mainA₂ (hready i hic).gt_one (Scale.inductionScale_le _ hp1.le i)
              (Scale.vertexMass_nonneg _) hC mainA₁_nonneg mainA₂_nonneg hCA
              (by linarith [(hready i hic).log_large])
              ((le_max_right _ _).trans (hready' i hic).log_large)
            have hfinal := hscalar.trans habs
            simpa only [hpc,P,← main_cost_eq_scale] using hfinal
          · apply terminal
            calc
              _ ≤ mainP*H.pieceMass i := hprefix H.count le_rfl (by omega)
              _ ≤ mainP*(2*P.vertices.card) := mul_le_mul_of_nonneg_left
                (H.pieceMass_two hp1 (fun j hj => (hready j hj).log_large) i hic) mainP_pos.le
              _ = _ := by ring
  intro V _ G
  exact hmain (Fintype.card V) V rfl G

theorem erdos_gallai : MainStatement := by
  obtain ⟨C,hC,hcost⟩ := main_cost_bound
  refine ⟨C,hC,?_⟩
  intro n G
  refine ⟨decompositionCost G,decompositionCost_spec G,?_⟩
  have hh := hcost (Fin n) G
  simp only [Fintype.card_fin] at hh
  have hp := mul_le_mul_of_nonneg_left (Batch.inductionPhi_bounds n).2
    (mul_nonneg hC.le (Nat.cast_nonneg n : (0:ℝ) ≤ _))
  nlinarith only [hh,hp]

end
end ErdosGallai

end

end
end

end OAI
