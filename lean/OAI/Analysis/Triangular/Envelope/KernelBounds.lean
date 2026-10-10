import OAI.Analysis.Triangular.Construction.TailJetVector
import OAI.Analysis.Triangular.Envelope.TailEnvelopeSeries
import OAI.Analysis.Triangular.Envelope.EnvelopeSums

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma fullTailW_nonneg (i : Fin 15) (d : Fin 2) : 0 ≤ fullTailW i d := by
  unfold fullTailW
  split_ifs
  · apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro l _
    split_ifs with hi
    · apply mul_nonneg _ (norm_nonneg _)
      have hh : (i.val+1:ℝ)  ≤  frequencyDistance l := by exact_mod_cast hi
      linarith
    · rfl
  · positivity
lemma finiteNode_node (i : Fin 10) : 0<finiteNode i ∧ (finiteNode i)%36 ∈ residues := by
  revert i; decide +kernel
lemma finiteNode_Qpos (i : Fin 10) : 0<Q (finiteNode i) := by
  have hh := FiniteCertificate.Q_node_bounds _ (finiteNode_node i).2
  linarith [hh.1]
lemma Node.Qpos (n : Node) : 0<Q n.val := by
  have hh := FiniteCertificate.Q_node_bounds _ n.property.2
  linarith [hh.1]
lemma finite_tail_column_bound (n : ℤ) (c : Fin 2) :
    (∑ m : Fin 10, ∑ d : Fin 2, |tailJet h H (finiteNode m) n c d|) < 335 := by
  apply lt_of_le_of_lt _ (by simpa using FiniteCertificate.finiteTailEnvelope_bound c)
  calc
    _  ≤  ∑ m : Fin 10, ∑ i : Fin 15,
        normJetEnvelope h H (finiteNode m) (frequency ⟨i.val+16,by omega⟩)*fullTailW i c := by
      apply Finset.sum_le_sum
      intro m _
      exact tailJet_pair_bound 0 1 _ n (by have h := (finiteNode_node m).1; omega) (finiteNode_Qpos m) c
    _ = finiteTailEnvelope c := by
      rw [Finset.sum_comm]
      simp only [finiteTailEnvelope,finiteEnvelopeSum,damping,↓reduceIte,Fin.val_zero,Fin.val_one,one_ne_zero,Finset.sum_mul]
lemma paired_summable_bound {α : Type*} (K : α → Fin 2 → ℝ) (G : α → ℝ)
    (hG : Summable G) (hdom : ∀ a, (∑ d : Fin 2, |K a d|) ≤ G a) :
    Summable (fun p : α × Fin 2 => |K p.1 p.2|) ∧
      (∑' p : α × Fin 2, |K p.1 p.2|)  ≤  ∑' a, G a := by
  have hs : Summable (fun a => ∑ d : Fin 2, |K a d|) :=
    hG.of_nonneg_of_le (fun a => Finset.sum_nonneg (fun d _ => abs_nonneg _)) hdom
  have hp : Summable (fun p : α × Fin 2 => |K p.1 p.2|) := by
    apply (summable_prod_of_nonneg (fun _ => abs_nonneg _)).mpr
    exact ⟨fun a => (hasSum_fintype _).summable,by simpa only [tsum_fintype] using hs⟩
  refine ⟨hp,?_⟩
  rw [hp.tsum_prod]
  simp only [tsum_fintype]
  exact hs.tsum_le_tsum hdom hG
lemma tail_atom_column_bounds (q v : Fin 2) (S : Fin 31 → ℂ) :
    Summable (fun p : TailNode × Fin 2 => |jet (damping q) (damping v) p.1.val.val p.2 S|) ∧
    (∑' p : TailNode × Fin 2, |jet (damping q) (damping v) p.1.val.val p.2 S|)  ≤ 
      ∑ j : Fin 31, tailEnvelopeSum q v j*‖S j‖ := by
  have hs (j : Fin 31) : Summable (fun n : TailNode =>
      normJetEnvelope (damping q) (damping v) n.val.val (frequency j)*‖S j‖) :=
    (summable_tailEnvelope q v (abs_le.mpr (frequency_mem j))).mul_right _
  have hsum := summable_sum (s:=Finset.univ) (fun j _ => hs j)
  have hh := paired_summable_bound (fun n d => jet (damping q) (damping v) n.val.val d S)
    (fun n : TailNode => ∑ j : Fin 31, normJetEnvelope (damping q) (damping v) n.val.val (frequency j)*‖S j‖)
    hsum (fun n => jet_pair_bound _ _ _ n.val.Qpos S)
  refine ⟨hh.1,?_⟩
  calc
    _  ≤  _ := hh.2
    _ = _ := by
      rw [Summable.tsum_finsetSum (fun j _ => hs j)]
      simp only [tsum_mul_right,tsum_tailEnvelope]
lemma tail_tail_column_bounds (q v : Fin 2) (n : ℤ) (c : Fin 2) :
    Summable (fun p : TailNode × Fin 2 => |tailJet (damping q) (damping v) p.1.val.val n c p.2|) ∧
    (∑' p : TailNode × Fin 2, |tailJet (damping q) (damping v) p.1.val.val n c p.2|)  ≤ 
      ∑ i : Fin 15, tailEnvelopeSum q v ⟨i.val+16,by omega⟩*fullTailW i c := by
  have hs (i : Fin 15) : Summable (fun m : TailNode =>
      normJetEnvelope (damping q) (damping v) m.val.val (frequency ⟨i.val+16,by omega⟩)*fullTailW i c) :=
    (summable_tailEnvelope q v (abs_le.mpr (frequency_mem _))).mul_right _
  have hsum := summable_sum (s:=Finset.univ) (fun i _ => hs i)
  have hh := paired_summable_bound (fun m d => tailJet (damping q) (damping v) m.val.val n c d)
    (fun m : TailNode => ∑ i : Fin 15, normJetEnvelope (damping q) (damping v) m.val.val (frequency ⟨i.val+16,by omega⟩)*fullTailW i c)
    hsum (fun m => tailJet_pair_bound q v _ n (by have h := m.val.property.1; omega) m.val.Qpos c)
  refine ⟨hh.1,?_⟩
  calc
    _  ≤  _ := hh.2
    _ = _ := by
      rw [Summable.tsum_finsetSum (fun i _ => hs i)]
      simp only [tsum_mul_right,tsum_tailEnvelope]
lemma tail_finite_column_bound (c : Fin 22) :
    (∑' p : TailNode × Fin 2, |jet H h p.1.val.val p.2 (finiteColumn ⟨c.val,by omega⟩)|) < 7/10^15 := by
  exact (tail_atom_column_bounds 1 0 _).2.trans_lt (by norm_num [tailFiniteEnvelope,damping,H,h] at ⊢; simpa [tailFiniteEnvelope] using FiniteCertificate.tailFiniteEnvelope_bound c)
lemma tail_tail_column_bound (n : ℤ) (c : Fin 2) :
    (∑' p : TailNode × Fin 2, |tailJet h h p.1.val.val n c p.2|) < 23/10^9 := by
  exact (tail_tail_column_bounds 0 0 n c).2.trans_lt (by norm_num [tailTailEnvelope,damping,H,h] at ⊢; simpa [tailTailEnvelope] using FiniteCertificate.tailTailEnvelope_bound c)
lemma tail_constant_column_bound :
    (∑' p : TailNode × Fin 2, |jet h h p.1.val.val p.2 fourierCoeff|) < 127/10^9 := by
  exact (tail_atom_column_bounds 0 0 _).2.trans_lt (by norm_num [tailConstantEnvelope,damping,H,h] at ⊢; simpa [tailConstantEnvelope] using FiniteCertificate.tailConstantEnvelope_bound)
end AtomicTriangular.Construction
end

end OAI
