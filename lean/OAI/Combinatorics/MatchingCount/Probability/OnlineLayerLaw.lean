import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OutputLengthBound
import OAI.Combinatorics.MatchingCount.Algorithm.TreeWeights
import OAI.Combinatorics.MatchingCount.Machines.OnlineUniform

namespace OAI

namespace MatchingFPRAS.PhysicalStream
lemma qaverage_const {A : Type} [Fintype A] [Nonempty A] (q : ℚ) :
    qaverage (fun _ : A=>q)=q := by
  simp only [qaverage,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have h : (Fintype.card A:ℚ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
end MatchingFPRAS.PhysicalStream

namespace MatchingFPRAS.OnlineTrial
open PhysicalStream TreeTyped TreeFraction ExecutableSource ExecutableScaling Transport UnitRefresh Enlargement

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {G : GraphInput} [Nontrivial (Fin G.n)]

lemma mean_drawAppend (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K)
    (L : FiniteTrial.Layer p j) {a : ℕ} (f : (Fin a→Bool)→L.Ω)
    (h : (L.append p hj).Ω→ℚ) :
    qaverage (fun b=>h (L.drawAppend p hj f b))=
      qaverage (fun c=>qaverage (fun b=>h ⟨f c,(L.state (f c)).drawStage p hj b⟩)) := by
  change qaverage ((fun c : (Fin a→Bool)×(Fin (FiniteTrial.stageBits p)→Bool)=>
    h ⟨f c.1,(L.state (f c.1)).drawStage p hj c.2⟩) ∘ pairBitsEquiv a (FiniteTrial.stageBits p))=_
  rw [qaverage_equiv,qaverage_prod]

lemma mean_layer_succ (p : Trial.Parameters G) {j : ℕ} (hj : j+1≤p.K)
    (h : (FiniteTrial.layers p (j+1) hj).Ω→ℚ) :
    qaverage (fun b=>h (FiniteTrial.drawLayer p (j+1) hj b))=
      qaverage (fun a=>qaverage (fun b=>h
        ⟨FiniteTrial.drawLayer p j (by omega) a,
          ((FiniteTrial.layers p j (by omega)).state (FiniteTrial.drawLayer p j (by omega) a)).drawStage p (by omega) b⟩)) := by
  change qaverage ((fun b=>h ((FiniteTrial.layers p j (by omega)).drawAppend p (by omega)
    (FiniteTrial.drawLayer p j (by omega)) b)) ∘ FiniteTrial.successorBitsEquiv j (FiniteTrial.stageBits p))=_
  rw [qaverage_equiv]
  exact mean_drawAppend p (by omega) (FiniteTrial.layers p j (by omega))
    (FiniteTrial.drawLayer p j (by omega)) h

noncomputable def product {j : ℕ} (p : Trial.Parameters G) (L : FiniteTrial.Layer p j) (x : L.Ω) : ℚ :=
  (Z (completeGraph G.n):ℚ)*∏ i,L.ratios x i
omit [Nontrivial (Fin G.n)] in
lemma product_nonneg [Nontrivial (Fin G.n)] {j : ℕ} (p : Trial.Parameters G) (L : FiniteTrial.Layer p j) (x : L.Ω) :
    0≤product p L x := mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _=>L.ratios_nonneg x i))
lemma product_append {j : ℕ} (p : Trial.Parameters G) (hj : j≤p.K) (L : FiniteTrial.Layer p j)
    (x : (L.append p hj).Ω) :
    product p (L.append p hj) x = product p L x.1 *
      (L.state x.1).ratioEstimate (RationalSource.sourceMarkedEquiv (L.state x.1).activity p.K ∘ x.2) := by
  unfold product FiniteTrial.Layer.append
  dsimp only
  rw [Fin.prod_snoc,mul_assoc]

end MatchingFPRAS.OnlineTrial

end OAI
