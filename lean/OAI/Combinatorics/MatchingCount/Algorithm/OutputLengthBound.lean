import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.FiniteStage
import OAI.Combinatorics.MatchingCount.Algorithm.RationalStart
import OAI.Combinatorics.MatchingCount.Algorithm.RationalCounts
import OAI.Combinatorics.MatchingCount.Algorithm.EmpiricalDenom

namespace OAI

namespace MatchingFPRAS
open Finset

lemma Perfect.vertices_le_twice_edges {G : GraphInput} {M : Finset (Fin G.n × Fin G.n)}
    (h : Perfect G M) : G.n≤2*G.edges.card := by
  classical
  have hs : (univ : Finset (Fin G.n)) ⊆ G.edges.image Prod.fst ∪ G.edges.image Prod.snd := by
    intro v _
    obtain ⟨e,⟨he,hi⟩,_⟩:=h.2 v
    rcases hi with hi|hi
    · exact mem_union_left _ (mem_image.mpr ⟨e,h.1 he,hi⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨e,h.1 he,hi⟩)
  calc
    G.n = (univ : Finset (Fin G.n)).card := by simp
    _ ≤ (G.edges.image Prod.fst ∪ G.edges.image Prod.snd).card := card_le_card hs
    _ ≤ (G.edges.image Prod.fst).card+(G.edges.image Prod.snd).card := card_union_le _ _
    _ ≤ G.edges.card+G.edges.card := Nat.add_le_add (card_image_le) (card_image_le)
    _ = _ := by omega
lemma positive_count_vertices (G : GraphInput) (hZ : 0<Z G) : G.n≤2*G.edges.card := by
  classical
  obtain ⟨M,hM⟩:=card_pos.mp hZ
  exact ((mem_perfectMatchings G M).mp hM).vertices_le_twice_edges

lemma sparse_reject_zero (G : GraphInput) (h : 2*G.edges.card<G.n) : Z G=0 := by
  by_contra hz
  have hh:=positive_count_vertices G (Nat.pos_of_ne_zero hz)
  omega
lemma encodeNat_length_pos (n : ℕ) : 0<(encodeNat n).length := by simp [encodeNat]
lemma flatMap_length_ge {α β : Type*} (f : α → List β) (hf : ∀ a,0<(f a).length)
    (L : List α) : L.length≤(L.flatMap f).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha:=hf a
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega
lemma edges_le_input_length (G : GraphInput) (e d : ℚ) : G.edges.card≤(encodeInput G e d).length := by
  classical
  let L := (G.edges.map toLex.toEmbedding).sort (· ≤ ·)
  let f := fun a : Lex (Fin G.n × Fin G.n)=>encodeNat (ofLex a).1.val ++ encodeNat (ofLex a).2.val
  have hf : ∀ a,0<(f a).length := by
    intro a
    have hh:=encodeNat_length_pos (ofLex a).1.val
    simpa only [f,List.length_append] using (lt_of_lt_of_le hh (Nat.le_add_right _ _))
  have hh:=flatMap_length_ge f hf L
  have hL : L.length=G.edges.card := by simp [L]
  rw [hL] at hh
  unfold encodeInput
  change G.edges.card≤(encodeNat G.n ++ encodeNat G.edges.card ++ L.flatMap f ++ encodeRat e ++ encodeRat d).length
  simp only [List.length_append]
  omega
lemma nonzero_vertices_le_input_twice (G : GraphInput) (e d : ℚ) (h : 2*G.edges.card≥G.n) :
    G.n≤2*(encodeInput G e d).length :=
  h.trans (Nat.mul_le_mul_left 2 (edges_le_input_length G e d))
end MatchingFPRAS

namespace MatchingFPRAS.Counting
lemma sigma_inv_polynomial (D K : ℕ) (e : ℚ) (he : 0<e) :
    (sigma D K e)⁻¹ ≤ 10000000*D+1000*K*(⌈e⁻¹⌉₊:ℚ) := by
  have hec : e⁻¹≤(⌈e⁻¹⌉₊:ℚ) := Nat.le_ceil _
  unfold sigma
  rw [min_def]
  split_ifs
  · have hh : (alpha/(100*(D:ℚ)))⁻¹=10000000*D := by norm_num [alpha,div_eq_mul_inv,mul_inv_rev]; ring
    rw [hh]
    exact le_add_of_nonneg_right (by positivity)
  · rw [inv_div]
    calc
      (1000*(K:ℚ))/e = 1000*K*e⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 1000*K*(⌈e⁻¹⌉₊:ℚ) := mul_le_mul_of_nonneg_left hec (by positivity)
      _ ≤ _ := le_add_of_nonneg_left (by positivity)
end MatchingFPRAS.Counting
namespace MatchingFPRAS.Trial
open Enlargement

lemma Parameters.N_polynomial {G : GraphInput} (p : Parameters G) :
    p.N≤G.n+G.n^2*(4*(2*p.K+2)) := by
  have h := Fintype.card_subtype_le (fun a : Fin G.n × Fin G.n=>a.1<a.2)
  change Fintype.card (LogicalEdge (Fin G.n))≤Fintype.card (Fin G.n × Fin G.n) at h
  simp only [Fintype.card_prod,Fintype.card_fin] at h
  simp only [Parameters.N,SourceVertex,RealGeometry.Vertex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  simpa only [pow_two] using Nat.add_le_add_left (Nat.mul_le_mul_right (4*(2*p.K+2)) h) G.n
lemma Parameters.D_polynomial {G : GraphInput} (p : Parameters G) :
    p.D=100*p.N^2*(100000000*(G.n+1)^4) := by
  simp only [Parameters.D,sourceD,Parameters.N,Fintype.card_fin]
lemma Parameters.S_polynomial {G : GraphInput} [Nontrivial (Fin G.n)] (p : Parameters G) :
    p.S≤10*(10000000*p.D+1000*p.K*⌈p.epsilon⁻¹⌉₊)^2*(G.n+p.K+1) := by
  rw [←FiniteTrial.sampleCount_eq p]
  unfold FiniteTrial.sampleCount
  apply Nat.ceil_le.mpr
  have hh:=Counting.sigma_inv_polynomial p.D p.K p.epsilon p.epsilon_pos
  have heq : FiniteTrial.sourceD (G:=G) p.K=p.D := FiniteTrial.sourceD_eq (G:=G) p.K
  rw [←heq] at hh
  have hh0 : 0≤(Counting.sigma (FiniteTrial.sourceD (G:=G) p.K) p.K p.epsilon)⁻¹ :=
    inv_nonneg.mpr (Counting.sigma_nonneg _ _ _ p.epsilon_pos.le)
  push_cast
  gcongr
  simpa only [heq] using hh
end MatchingFPRAS.Trial

namespace MatchingFPRAS.BitArithmetic
lemma size_add_le (a b : ℕ) : (a+b).size≤a.size+b.size+1 := by
  apply Nat.size_le.mpr
  have ha:=Nat.lt_size_self a
  have hb:=Nat.lt_size_self b
  have h₁ : (2:ℕ)^a.size≤2^(a.size+b.size) := Nat.pow_le_pow_right (by decide) (by omega)
  have h₂ : (2:ℕ)^b.size≤2^(a.size+b.size) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_succ]
  omega
lemma complete_count_size (n : ℕ) : (Z (completeGraph n)+1).size≤(n/2)*n.size+3 := by
  have hb : Z (completeGraph n)≤n^(n/2) := by
    rw [GraphBridge.complete_count]
    exact UnitRefresh.pairingCount_le_half_power n
  have hh:=size_add_le (Z (completeGraph n)) 1
  have hs:=Nat.size_le_size hb
  have hp:=size_pow_le n (n/2)
  have h1 : (1:ℕ).size=1 := by decide
  omega
end MatchingFPRAS.BitArithmetic
namespace MatchingFPRAS.Amplification
lemma median_mem {k : ℕ} (out : Fin (2*k+1) → ℚ) : ∃ i,median out=out i := by
  unfold median sortedValue
  have hp:=List.mergeSort_perm (List.ofFn out) (· ≤ ·)
  have hx : (sortedList out)[k]'(by rw [sortedList_length]; omega)∈List.ofFn out :=
    hp.mem_iff.mp (List.getElem_mem _)
  obtain ⟨i,hi⟩:=List.mem_ofFn.mp hx
  exact ⟨i,hi.symm⟩
end MatchingFPRAS.Amplification
namespace MatchingFPRAS.FiniteTrial
open BitArithmetic

variable {G : GraphInput} [Nontrivial (Fin G.n)]
noncomputable def outputLengthBound (p : Trial.Parameters G) : ℕ :=
  2*((G.n/2)*G.n.size+3+p.K*(2*p.empiricalBound.size+1)+1)+3
lemma output_encode_length (p : Trial.Parameters G) (x : (layers p p.K le_rfl).Ω) :
    (encodeRat (output p x)).length≤outputLengthBound p := by
  have h₁:=(output_bits p x).encode_length
  have h₂:=size_mul_le (Z (completeGraph G.n)+1) ((p.empiricalBound^2)^p.K)
  have h₃:=complete_count_size G.n
  have h₄:=size_pow_le (p.empiricalBound^2) p.K
  have h₅:=size_pow_le p.empiricalBound 2
  have hb : ((Z (completeGraph G.n)+1)*(p.empiricalBound^2)^p.K).size≤
      (G.n/2)*G.n.size+3+p.K*(2*p.empiricalBound.size+1)+1 := by
    calc
      _ ≤ (Z (completeGraph G.n)+1).size+((p.empiricalBound^2)^p.K).size := h₂
      _ ≤ (G.n/2)*G.n.size+3+(p.K*(p.empiricalBound^2).size+1) := Nat.add_le_add h₃ h₄
      _ ≤ _ := by have hh:=Nat.mul_le_mul_left p.K h₅; omega
  unfold outputLengthBound
  omega
lemma amplifiedOutput_encode_length (p : Trial.Parameters G) (δ : ℚ)
    (x : Fin (2*Amplification.halfRepetitions δ+1) → (layers p p.K le_rfl).Ω) :
    (encodeRat (amplifiedOutput p δ x)).length≤outputLengthBound p := by
  obtain ⟨i,hi⟩:=Amplification.median_mem (fun i=>output p (x i))
  change (encodeRat (Amplification.median (fun i=>output p (x i)))).length≤_
  rw [hi]
  exact output_encode_length p (x i)
end MatchingFPRAS.FiniteTrial

namespace MatchingFPRAS.Transport
open Finset

lemma clog_two_le_self (m : ℕ) : Nat.clog 2 m ≤ m :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=m)).le
lemma bitPrecision_le (R : ℕ) (η : ℚ) : bitPrecision R η ≤ R*⌈η⁻¹⌉₊ :=
  clog_two_le_self _
lemma sym2_card_le_square (V : Type*) [Fintype V] : Fintype.card (Sym2 V) ≤ (Fintype.card V)^2 := by
  simpa only [Fintype.card_prod,pow_two] using Fintype.card_le_of_surjective _ (Sym2.mk_surjective (α:=V))
lemma bagEdge_card_le {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]
    (bags : V → Finset L) [Fintype (BagEdge bags)] :
    Fintype.card (BagEdge bags) ≤ (Fintype.card V)^2*Fintype.card L := by
  classical
  have hi : Function.Injective (fun e : BagEdge bags=>e.val.val) :=
    Subtype.val_injective.comp Subtype.val_injective
  exact (Fintype.card_le_of_injective _ hi).trans (by
    rw [Fintype.card_prod]
    exact Nat.mul_le_mul_right _ (sym2_card_le_square V))
def tierPolynomial (N D K : ℕ) := N^2*(D+2*K+2)
def lambdaPolynomial (N D K T : ℕ) := 10*N*ladderQ N D*(T+1)*(K+(N*D+2)+1)
def stepsPolynomial (N D K m : ℕ) :=
  20*ladderL N D*ladderM N D (tierPolynomial N D K)*
    (lambdaPolynomial N D K (tierPolynomial N D K)+m+1)
def edgePolynomial (N K : ℕ) := N^2*((2*K+1)*N)
def scanErrorPolynomial (N D K : ℕ) :=
  2*(1+ladderM N D (tierPolynomial N D K))+
  4*(8*(edgePolynomial N K)^2+4*edgePolynomial N K+3)+2*N^2*((2*K+1)*N)
def totalBitsPolynomial (N D K m H : ℕ) :=
  let t:=stepsPolynomial N D K m
  let R:=scanErrorPolynomial N D K
  t*((t*R*H)+(t*R*H+N*(t*R*H)))+edgePolynomial N K*(6*edgePolynomial N K*H)
lemma endpoint_le_polynomial (N D K : ℕ) (hN : 0<N) : endpoint N D K hN ≤ tierPolynomial N D K := by
  rw [endpoint_eq]
  apply (ladderTier_le N D K hN).trans
  unfold tierBound tierPolynomial
  gcongr
  exact clog_two_le_self D
lemma lambda_le_polynomial (N D K T : ℕ) : ladderLambda N D K T ≤ lambdaPolynomial N D K T := by
  unfold ladderLambda lambdaPolynomial
  gcongr
  exact clog_two_le_self _
lemma discreteSteps_le_polynomial (N D K T m : ℕ) (hT : T ≤ tierPolynomial N D K) :
    discreteLadderSteps N D K T m ≤ stepsPolynomial N D K m := by
  have hl : ladderLambda N D K T ≤ lambdaPolynomial N D K (tierPolynomial N D K) :=
    (lambda_le_polynomial N D K T).trans (by unfold lambdaPolynomial; gcongr)
  have hm : ladderM N D T ≤ ladderM N D (tierPolynomial N D K) := by unfold ladderM; gcongr
  unfold discreteLadderSteps stepsPolynomial
  gcongr
  exact clog_two_le_self m
end MatchingFPRAS.Transport
namespace MatchingFPRAS.RationalSource
open Transport Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
lemma edge_card_polynomial (w : V → V → ℚ) (K : ℕ) :
    Fintype.card (BagEdge (bags w K)) ≤ edgePolynomial (Fintype.card (SourceVertex V K)) K := by
  apply (bagEdge_card_le (bags w K)).trans
  unfold edgePolynomial
  exact Nat.mul_le_mul_left _ (label_card w K)
lemma scan_error_polynomial (w : V → V → ℚ) (K D T : ℕ)
    (hT : T ≤ tierPolynomial (Fintype.card (SourceVertex V K)) D K) :
    scanErrorNumerator (SourceVertex V K) (Label w K) (bags w K) T
      (ladderQ (Fintype.card (SourceVertex V K)) D) ≤ scanErrorPolynomial (Fintype.card (SourceVertex V K)) D K := by
  have he:=edge_card_polynomial w K
  have hl:=label_card w K
  unfold scanErrorNumerator scanErrorPolynomial ladderM
  gcongr
open Transport Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
def samplerBitCount (w : V → V → ℚ) (K D m : ℕ) (hN : 0<Fintype.card (SourceVertex V K)) (η : ℚ) : ℕ :=
  let N:=Fintype.card (SourceVertex V K)
  let T:=endpoint N D K hN
  let t:=discreteLadderSteps N D K T m
  t*scanBitCount N (bitPrecision (t*scanErrorNumerator (SourceVertex V K) (Label w K) (bags w K) T (ladderQ N D)) η)+
    Fintype.card (BagEdge (bags w K))*bitPrecision (6*Fintype.card (BagEdge (bags w K))) η
lemma samplerBitCount_le (w : V → V → ℚ) (K D m : ℕ) (hN : 0<Fintype.card (SourceVertex V K)) (η : ℚ) :
    samplerBitCount w K D m hN η ≤ totalBitsPolynomial (Fintype.card (SourceVertex V K)) D K m ⌈η⁻¹⌉₊ := by
  let N:=Fintype.card (SourceVertex V K)
  let T:=endpoint N D K hN
  let t:=discreteLadderSteps N D K T m
  let R:=scanErrorNumerator (SourceVertex V K) (Label w K) (bags w K) T (ladderQ N D)
  have hT : T ≤ tierPolynomial N D K := endpoint_le_polynomial N D K hN
  have ht : t ≤ stepsPolynomial N D K m := discreteSteps_le_polynomial N D K T m hT
  have hR : R ≤ scanErrorPolynomial N D K := scan_error_polynomial w K D T hT
  have hE:=edge_card_polynomial w K
  have hk : bitPrecision (t*R) η ≤ stepsPolynomial N D K m*scanErrorPolynomial N D K*⌈η⁻¹⌉₊ :=
    (bitPrecision_le _ _).trans (by gcongr)
  have hm : bitPrecision (6*Fintype.card (BagEdge (bags w K))) η ≤ 6*edgePolynomial N K*⌈η⁻¹⌉₊ :=
    (bitPrecision_le _ _).trans (by gcongr)
  change t*scanBitCount N (bitPrecision (t*R) η)+Fintype.card (BagEdge (bags w K))*bitPrecision (6*Fintype.card (BagEdge (bags w K))) η ≤ _
  dsimp only [totalBitsPolynomial,scanBitCount]
  gcongr
end MatchingFPRAS.RationalSource

namespace MatchingFPRAS.Variation
open Transport

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
omit [Fintype C] in
lemma imageLaw_ignore_right [Nonempty B] (f : A → C) :
    imageLaw (fun x : A×B=>f x.1)=imageLaw f := by
  have hh:=imageLaw_comp_equiv (Equiv.prodComm A B) (fun x : B×A=>f x.2)
  exact hh.trans (imageLaw_ignore f)
def paddedBits {k B : ℕ} (h : k≤B) :
    (Fin B → Bool) ≃ ((Fin k → Bool) × (Fin (B-k) → Bool)) :=
  (Equiv.arrowCongr (finCongr (Nat.add_sub_of_le h).symm) (Equiv.refl Bool)).trans (pairBitsEquiv k (B-k))
def padSampler {k B : ℕ} (h : k≤B) (f : (Fin k → Bool) → A) : (Fin B → Bool) → A :=
  fun bits=>f ((paddedBits h bits).1)
omit [Fintype A] in
lemma padSampler_law {k B : ℕ} (h : k≤B) (f : (Fin k → Bool) → A) :
    imageLaw (padSampler h f)=imageLaw f :=
  (imageLaw_comp_equiv (paddedBits h) (fun x=>f x.1)).trans (imageLaw_ignore_right f)
noncomputable def markedBitsEquiv (E : Type*) [Fintype E] (t k : ℕ) :
    (Fin (t+Fintype.card E*k) → Bool) ≃ ((Fin t → Bool) × (E → Fin k → Bool)) :=
  (pairBitsEquiv t (Fintype.card E*k)).trans (Equiv.prodCongr (Equiv.refl _)
    ((matrixBitsEquiv (Fintype.card E) k).trans
      (Equiv.arrowCongr (Fintype.equivFin E).symm (Equiv.refl _))))
end MatchingFPRAS.Variation
namespace MatchingFPRAS.RationalSource
open Transport Enlargement Variation

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (BagPM (bags w K)) := Fintype.ofFinite _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (Marked w K) := Fintype.ofFinite _
noncomputable local instance (w : V → V → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _
noncomputable local instance (w : V → V → ℚ) (K t k : ℕ) :
    Fintype ((Fin t → Bool) × (BagEdge (bags w K) → Fin k → Bool)) := Fintype.ofFinite _
noncomputable def bitSampler (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :
    (Fin (samplerBitCount w K D m hN η) → Bool) → SourceMarked (fun x y=>(w x y:ℝ)) K :=
  (sourceMarkedEquiv w K).symm ∘ markedSampler w hw K D m hD hN h hq M η ∘
    markedBitsEquiv (BagEdge (bags w K)) _ _
lemma bitSampler_law (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :
    imageLaw (bitSampler w hw K D m hD hN h hq M η)=finiteSourceLaw w hw K D m hD hN h hq M η := by
  dsimp only [bitSampler,samplerBitCount]
  erw [←Function.comp_assoc,imageLaw_comp_equiv,imageLaw_output_equiv]
  rfl
noncomputable def fixedSampler (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :
    (Fin (totalBitsPolynomial (Fintype.card (SourceVertex V K)) D K m ⌈η⁻¹⌉₊) → Bool) →
      SourceMarked (fun x y=>(w x y:ℝ)) K :=
  padSampler (samplerBitCount_le w K D m hN η) (bitSampler w hw K D m hD hN h hq M η)
lemma fixedSampler_law (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ)
    (hD : 0<D) (hN : 0<Fintype.card (SourceVertex V K))
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) :
    imageLaw (fixedSampler w hw K D m hD hN h hq M η)=finiteSourceLaw w hw K D m hD hN h hq M η := by
  rw [fixedSampler,padSampler_law,bitSampler_law]
end MatchingFPRAS.RationalSource

namespace MatchingFPRAS.Variation
open Finset
open scoped Classical

variable {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X]
variable {E : X → Type*} [∀ x,Fintype (E x)]
omit [∀ x,Fintype (E x)] in
lemma imageLaw_sigma_pair (f : A → X) (g : ∀ x,B → E x) :
    imageLaw (fun z : A×B=>(⟨f z.1,g (f z.1) z.2⟩ : Sigma E))=
      sigmaLift (imageLaw f) (fun x=>imageLaw (g x)) := by
  rw [imageLaw_adaptive_pair f (fun x b=>(⟨x,g x b⟩ : Sigma E))]
  funext ⟨x,y⟩
  unfold bind sigmaLift
  dsimp only
  have he : imageLaw (fun b=>(⟨x,g x b⟩ : Sigma E)) ⟨x,y⟩=imageLaw (g x) y := by
    unfold imageLaw push
    simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and]
  rw [←he]
  apply sum_eq_single x
  · intro a _ ha
    have hz : imageLaw (fun b=>(⟨a,g a b⟩ : Sigma E)) ⟨x,y⟩=0 := by
      unfold imageLaw push
      apply sum_eq_zero
      intro b _
      exact ite_eq_right (fun hh=>ha (congrArg Sigma.fst hh))
    rw [hz,mul_zero]
  · simp
end MatchingFPRAS.Variation

namespace MatchingFPRAS.FiniteTrial
open Transport Enlargement Variation Adaptive

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _
noncomputable def oneBits (p : Trial.Parameters G) : ℕ :=
  totalBitsPolynomial p.N p.D p.K (1000*p.K*p.S) ⌈(1/(1000*p.K*p.S):ℚ)⁻¹⌉₊
omit [Nontrivial (Fin G.n)] in
lemma oneBits_eq (p : Trial.Parameters G) : oneBits p=totalBitsPolynomial p.N p.D p.K (1000*p.K*p.S) (1000*p.K*p.S) := by
  unfold oneBits
  congr 1
  rw [one_div,inv_inv]
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using (Nat.ceil_natCast (R:=ℚ) (1000*p.K*p.S))
noncomputable def ScaleState.drawOne (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K) (s : ScaleState G j) :
    (Fin (oneBits p) → Bool) → SourceMarked (fun a b=>(s.activity a b:ℝ)) p.K :=
  RationalSource.fixedSampler s.activity s.activity_pos p.K
    (Enlargement.sourceD (V:=Fin G.n) p.K) (1000*p.K*p.S)
    (sourceD_one p.K) Fintype.card_pos (s.cap hj) p.q_pos
    (RationalSource.startMatching s.activity p.K p.even) (1/(1000*p.K*p.S))
lemma ScaleState.drawOne_law (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K) (s : ScaleState G j) :
    imageLaw (s.drawOne p hj)=(s.runLaw p hj).mass := by
  exact RationalSource.fixedSampler_law _ _ _ _ _ _ _ _ _ _ _
noncomputable def stageBits (p : Trial.Parameters G) : ℕ := p.S*oneBits p
noncomputable def ScaleState.drawStage (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K) (s : ScaleState G j) :
    (Fin (stageBits p) → Bool) → Fin p.S → SourceMarked (fun a b=>(s.activity a b:ℝ)) p.K :=
  (fun b i=>s.drawOne p hj (b i)) ∘ matrixBitsEquiv p.S (oneBits p)
lemma ScaleState.drawStage_law (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K) (s : ScaleState G j) :
    imageLaw (s.drawStage p hj)=(s.sampleLaw p hj).mass := by
  unfold ScaleState.drawStage
  erw [imageLaw_comp_equiv,imageLaw_componentwise]
  rw [ScaleState.drawOne_law]
  rfl

open Transport Enlargement Variation Adaptive

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _
noncomputable def Layer.drawAppend (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K)
    (L : Layer p j) {a : ℕ} (f : (Fin a → Bool) → L.Ω) :
    (Fin (a+stageBits p) → Bool) → (L.append p hj).Ω :=
  fun b =>
    let c : (Fin a → Bool) × (Fin (stageBits p) → Bool) := pairBitsEquiv a (stageBits p) b
    (⟨f c.1,(L.state (f c.1)).drawStage p hj c.2⟩ :
      Σ x : L.Ω, Fin p.S → SourceMarked (fun v w=>((L.state x).activity v w:ℝ)) p.K)
lemma Layer.drawAppend_law (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K)
    (L : Layer p j) {a : ℕ} (f : (Fin a → Bool) → L.Ω) (hf : imageLaw f=L.law.mass) :
    imageLaw (L.drawAppend p hj f)=(L.append p hj).law.mass := by
  change imageLaw ((fun b : (Fin a → Bool) × (Fin (stageBits p) → Bool) =>
    (⟨f b.1,(L.state (f b.1)).drawStage p hj b.2⟩ :
      Σ x : L.Ω, Fin p.S → SourceMarked (fun v w=>((L.state x).activity v w:ℝ)) p.K)) ∘
    pairBitsEquiv a (stageBits p)) = _
  erw [imageLaw_comp_equiv]
  change imageLaw _ = sigmaLift L.law.mass (fun x=>(L.state x).sampleLaw p hj |>.mass)
  rw [imageLaw_sigma_pair f (fun x=>(L.state x).drawStage p hj)]
  simp_rw [ScaleState.drawStage_law]
  rw [hf]
def successorBitsEquiv (j B : ℕ) : (Fin ((j+1)*B) → Bool) ≃ (Fin (j*B+B) → Bool) :=
  Equiv.arrowCongr (finCongr (Nat.succ_mul j B)) (Equiv.refl Bool)
noncomputable def drawLayer (p : Trial.Parameters G) : (j : ℕ) → (hj : j≤p.K) →
    (Fin (j*stageBits p) → Bool) → (layers p j hj).Ω
  | 0,_ => fun _=>PUnit.unit
  | j+1,hj => (layers p j (by omega)).drawAppend p (by omega) (drawLayer p j (by omega)) ∘ successorBitsEquiv j (stageBits p)
lemma drawLayer_law (p : Trial.Parameters G) (j : ℕ) (hj : j≤p.K) :
    imageLaw (drawLayer p j hj)=(layers p j hj).law.mass := by
  induction j with
  | zero =>
    change imageLaw (fun _ : Fin (0*stageBits p) → Bool=>PUnit.unit)=(firstLayer p).law.mass
    rw [imageLaw_subsingleton]
    funext x
    simp [uniform,firstLayer]
  | succ j ih =>
    unfold drawLayer
    erw [imageLaw_comp_equiv]
    exact Layer.drawAppend_law p (by omega) (layers p j (by omega)) _ (ih (by omega))
noncomputable def bitOutput (p : Trial.Parameters G) : (Fin (p.K*stageBits p) → Bool) → ℚ :=
  output p ∘ drawLayer p p.K le_rfl
lemma bitOutput_nonneg (p : Trial.Parameters G) (b : Fin (p.K*stageBits p) → Bool) :
    0≤bitOutput p b := output_nonneg p _
end MatchingFPRAS.FiniteTrial

namespace MatchingFPRAS.Variation
open Finset
open scoped Classical

variable {A B : Type*} [Fintype A] [Fintype B]
lemma event_push (p : A → ℝ) (f : A → B) (P : B → Prop) :
    event (push p f) P=event p (fun x=>P (f x)) := by
  unfold event push
  have h : (∑ y,if P y then ∑ x,if f x=y then p x else 0 else 0)=
      ∑ y,∑ x,if f x=y then (if P y then p x else 0) else 0 := by
    apply sum_congr rfl
    intro y _
    by_cases hy:P y <;> simp [hy]
  rw [h,sum_comm]
  simp
lemma event_imageLaw (f : A → B) (P : B → Prop) :
    event (imageLaw f) P=((univ.filter (fun x=>P (f x))).card:ℝ)/Fintype.card A := by
  rw [imageLaw,event_push]
  unfold event uniform
  rw [show (∑ x,if P (f x) then (1:ℝ)/Fintype.card A else 0)=
    (∑ x,if P (f x) then (1:ℝ) else 0)/Fintype.card A by
      simp only [sum_div,ite_div,zero_div]]
  simp
lemma event_complement (p : A → ℝ) (P : A → Prop) :
    event p P+event p (fun x=>¬P x)=∑ x,p x := by
  unfold event
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro x _
  by_cases hx:P x <;> simp [hx]
end MatchingFPRAS.Variation

namespace MatchingFPRAS.FiniteTrial
open Variation Adaptive Amplification Finset Transport
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
noncomputable def amplifiedBits (p : Trial.Parameters G) (δ : ℚ) : ℕ :=
  (2*halfRepetitions δ+1)*(p.K*stageBits p)
noncomputable def drawTrials (p : Trial.Parameters G) (δ : ℚ) :
    (Fin (amplifiedBits p δ) → Bool) → Fin (2*halfRepetitions δ+1) → (layers p p.K le_rfl).Ω :=
  (fun bits i=>drawLayer p p.K le_rfl (bits i)) ∘ matrixBitsEquiv (2*halfRepetitions δ+1) (p.K*stageBits p)
lemma drawTrials_law (p : Trial.Parameters G) (δ : ℚ) :
    imageLaw (drawTrials p δ)=((layers p p.K le_rfl).law.iid (2*halfRepetitions δ+1)).mass := by
  unfold drawTrials
  erw [imageLaw_comp_equiv,imageLaw_componentwise]
  rw [drawLayer_law]
  rfl
noncomputable def amplifiedBitOutput (p : Trial.Parameters G) (δ : ℚ) :
    (Fin (amplifiedBits p δ) → Bool) → ℚ := amplifiedOutput p δ ∘ drawTrials p δ
lemma amplifiedBitOutput_nonneg (p : Trial.Parameters G) (δ : ℚ)
    (b : Fin (amplifiedBits p δ) → Bool) : 0≤amplifiedBitOutput p δ b :=
  amplifiedOutput_nonneg p δ _
noncomputable def accurateBits (p : Trial.Parameters G) (δ : ℚ) : Finset (Fin (amplifiedBits p δ) → Bool) :=
  univ.filter fun b=>Accurate p (amplifiedBitOutput p δ b)
theorem amplifiedBitOutput_success (p : Trial.Parameters G) (hZ : 0<Z G) (δ : ℚ) (hδ : 0<δ) :
    ((accurateBits p δ).card:ℚ)/(2:ℚ)^(amplifiedBits p δ)≥1-δ := by
  have hf:=actual_finite_amplified_failure p hZ δ hδ
  have hc:=event_complement ((layers p p.K le_rfl).law.iid (2*halfRepetitions δ+1)).mass
    (fun x=>Accurate p (amplifiedOutput p δ x))
  rw [Law.total] at hc
  have hh : 1-(δ:ℝ) ≤ event ((layers p p.K le_rfl).law.iid (2*halfRepetitions δ+1)).mass
      (fun x=>Accurate p (amplifiedOutput p δ x)) := by
    change event _ (fun x=>¬Accurate p (amplifiedOutput p δ x))≤(δ:ℝ) at hf
    linarith only [hc,hf]
  rw [←drawTrials_law,event_imageLaw] at hh
  have he : Fintype.card (Fin (amplifiedBits p δ) → Bool)=2^(amplifiedBits p δ) := by simp
  rw [he] at hh
  change 1-(δ:ℝ) ≤ ((accurateBits p δ).card:ℝ)/(2^(amplifiedBits p δ):ℕ) at hh
  have hr : ((1-δ:ℚ):ℝ) ≤ (((((accurateBits p δ).card:ℚ)/(2:ℚ)^(amplifiedBits p δ)):ℚ):ℝ) := by
    push_cast
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
  exact Rat.cast_le.mp hr
end MatchingFPRAS.FiniteTrial

namespace MatchingFPRAS.BitComplexity

def PolynomiallyBounded (f : ℕ → ℕ) : Prop := ∃ C d : ℕ, ∀ x,1≤x → f x≤C*x^d
lemma PolynomiallyBounded.const (c : ℕ) : PolynomiallyBounded (fun _=>c) := by
  exact ⟨c,0,fun _ _=>by simp⟩
lemma PolynomiallyBounded.id : PolynomiallyBounded (fun x=>x) := by
  exact ⟨1,1,fun _ _=>by simp⟩
lemma PolynomiallyBounded.add {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun x=>f x+g x) := by
  obtain ⟨C,d,hf⟩:=hf
  obtain ⟨E,k,hg⟩:=hg
  refine ⟨C+E,d+k,fun x hx=>?_⟩
  have h₁ : x^d≤x^(d+k) := Nat.pow_le_pow_right hx (by omega)
  have h₂ : x^k≤x^(d+k) := Nat.pow_le_pow_right hx (by omega)
  calc
    _ ≤ C*x^d+E*x^k := Nat.add_le_add (hf x hx) (hg x hx)
    _ ≤ C*x^(d+k)+E*x^(d+k) := Nat.add_le_add (Nat.mul_le_mul_left C h₁) (Nat.mul_le_mul_left E h₂)
    _ = _ := (Nat.add_mul _ _ _).symm
lemma PolynomiallyBounded.mul {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun x=>f x*g x) := by
  obtain ⟨C,d,hf⟩:=hf
  obtain ⟨E,k,hg⟩:=hg
  refine ⟨C*E,d+k,fun x hx=>?_⟩
  calc
    _ ≤ (C*x^d)*(E*x^k) := Nat.mul_le_mul (hf x hx) (hg x hx)
    _ = _ := by rw [pow_add]; ac_rfl
lemma PolynomiallyBounded.pow {f : ℕ → ℕ} (hf : PolynomiallyBounded f) (k : ℕ) :
    PolynomiallyBounded (fun x=>(f x)^k) := by
  obtain ⟨C,d,hf⟩:=hf
  refine ⟨C^k,d*k,fun x hx=>?_⟩
  calc
    _ ≤ (C*x^d)^k := Nat.pow_le_pow_left (hf x hx) k
    _ = _ := by rw [mul_pow,pow_mul]
def boundK (x : ℕ) : ℕ := (2*x)*((2*x)*(2*x)+32*x)
def boundN (x : ℕ) : ℕ := 2*x+(2*x)^2*(4*(2*boundK x+2))
def boundD (x : ℕ) : ℕ := 100*(boundN x)^2*(100000000*(2*x+1)^4)
def boundS (x : ℕ) : ℕ := 10*(10000000*boundD x+1000*boundK x*x)^2*(2*x+boundK x+1)
def boundBits (x : ℕ) : ℕ := (10*(x+1)+1)*(boundK x*(boundS x*
  Transport.totalBitsPolynomial (boundN x) (boundD x) (boundK x) (1000*boundK x*boundS x) (1000*boundK x*boundS x)))
private lemma c (n : ℕ) : PolynomiallyBounded (fun _=>n) := PolynomiallyBounded.const n
private lemma X : PolynomiallyBounded (fun n=>n) := PolynomiallyBounded.id
lemma boundK_polynomial : PolynomiallyBounded boundK := by
  exact ((c 2).mul X).mul ((((c 2).mul X).mul ((c 2).mul X)).add ((c 32).mul X))
lemma boundN_polynomial : PolynomiallyBounded boundN := by
  exact ((c 2).mul X).add (((((c 2).mul X).pow 2)).mul ((c 4).mul (((c 2).mul boundK_polynomial).add (c 2))))
lemma boundD_polynomial : PolynomiallyBounded boundD := by
  exact ((c 100).mul (boundN_polynomial.pow 2)).mul ((c 100000000).mul ((((c 2).mul X).add (c 1)).pow 4))
lemma boundS_polynomial : PolynomiallyBounded boundS := by
  exact ((c 10).mul ((((c 10000000).mul boundD_polynomial).add (((c 1000).mul boundK_polynomial).mul X)).pow 2)).mul ((((c 2).mul X).add boundK_polynomial).add (c 1))
open Transport

lemma ladderL_polynomial {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun x=>ladderL (f x) (g x)) := by
  exact (((c (10^4)).mul hf).mul hg).pow 100
lemma ladderQ_polynomial {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun x=>ladderQ (f x) (g x)) := by
  exact (c 32).mul (ladderL_polynomial hf hg)
lemma ladderM_polynomial {f g h : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g)
    (hh : PolynomiallyBounded h) : PolynomiallyBounded (fun x=>ladderM (f x) (g x) (h x)) := by
  exact (hh.mul ((ladderQ_polynomial hf hg).pow 2)).add (ladderQ_polynomial hf hg)
lemma tier_polynomial {f g h : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g)
    (hh : PolynomiallyBounded h) : PolynomiallyBounded (fun x=>tierPolynomial (f x) (g x) (h x)) := by
  exact (hf.pow 2).mul ((hg.add ((c 2).mul hh)).add (c 2))
lemma edge_polynomial {f h : ℕ → ℕ} (hf : PolynomiallyBounded f) (hh : PolynomiallyBounded h) :
    PolynomiallyBounded (fun x=>edgePolynomial (f x) (h x)) := by
  exact (hf.pow 2).mul ((((c 2).mul hh).add (c 1)).mul hf)
lemma lambda_polynomial {f g h t : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g)
    (hh : PolynomiallyBounded h) (ht : PolynomiallyBounded t) :
    PolynomiallyBounded (fun x=>lambdaPolynomial (f x) (g x) (h x) (t x)) := by
  exact ((((c 10).mul hf).mul (ladderQ_polynomial hf hg)).mul (ht.add (c 1))).mul
    ((hh.add ((hf.mul hg).add (c 2))).add (c 1))
lemma steps_polynomial {f g h m : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g)
    (hh : PolynomiallyBounded h) (hm : PolynomiallyBounded m) :
    PolynomiallyBounded (fun x=>stepsPolynomial (f x) (g x) (h x) (m x)) := by
  have ht:=tier_polynomial hf hg hh
  exact (((c 20).mul (ladderL_polynomial hf hg)).mul (ladderM_polynomial hf hg ht)).mul
    (((lambda_polynomial hf hg hh ht).add hm).add (c 1))
lemma scan_polynomial {f g h : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g)
    (hh : PolynomiallyBounded h) : PolynomiallyBounded (fun x=>scanErrorPolynomial (f x) (g x) (h x)) := by
  have ht:=tier_polynomial hf hg hh
  have he:=edge_polynomial hf hh
  exact (((c 2).mul ((c 1).add (ladderM_polynomial hf hg ht))).add
    ((c 4).mul (((((c 8).mul (he.pow 2)).add ((c 4).mul he))).add (c 3)))).add
    (((c 2).mul (hf.pow 2)).mul ((((c 2).mul hh).add (c 1)).mul hf))
lemma total_polynomial {f g h m H : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g)
    (hh : PolynomiallyBounded h) (hm : PolynomiallyBounded m) (hH : PolynomiallyBounded H) :
    PolynomiallyBounded (fun x=>totalBitsPolynomial (f x) (g x) (h x) (m x) (H x)) := by
  have ht:=steps_polynomial hf hg hh hm
  have hR:=scan_polynomial hf hg hh
  have he:=edge_polynomial hf hh
  have ha:=(ht.mul hR).mul hH
  exact (ht.mul (ha.add (ha.add (hf.mul ha)))).add (he.mul (((c 6).mul he).mul hH))
lemma boundBits_polynomial : PolynomiallyBounded boundBits := by
  have hm:=((c 1000).mul boundK_polynomial).mul boundS_polynomial
  exact (((c 10).mul (X.add (c 1))).add (c 1)).mul (boundK_polynomial.mul
    (boundS_polynomial.mul (total_polynomial boundN_polynomial boundD_polynomial boundK_polynomial hm hm)))
end MatchingFPRAS.BitComplexity

namespace MatchingFPRAS.Transport
lemma totalBitsPolynomial_mono {N N' D D' K K' m m' H H' : ℕ}
    (hN : N ≤ N') (hD : D ≤ D') (hK : K ≤ K') (hm : m ≤ m') (hH : H ≤ H') :
    totalBitsPolynomial N D K m H ≤ totalBitsPolynomial N' D' K' m' H' := by
  unfold totalBitsPolynomial stepsPolynomial scanErrorPolynomial lambdaPolynomial tierPolynomial
    edgePolynomial ladderM ladderQ ladderL
  dsimp only
  gcongr
end MatchingFPRAS.Transport
namespace MatchingFPRAS.BitComplexity
open FiniteTrial Trial Transport Amplification

lemma parameters_K_le {G : GraphInput} (hn : 2 ≤ G.n) (heven : Even G.n)
    (e : ℚ) (he : 0<e) (he1 : e<1) (x : ℕ) (hnx : G.n ≤ 2*x) (hex : ⌈e⁻¹⌉₊ ≤ x) :
    (parameters G hn heven e he he1).K ≤ boundK x := by
  apply (Counting.leastSchedule_polynomial G.n hn e he he1).trans
  unfold Counting.schedulePolynomial boundK
  gcongr
lemma parameters_N_le {G : GraphInput} (p : Parameters G)
    (x : ℕ) (hnx : G.n ≤ 2*x) (hk : p.K ≤ boundK x) : p.N ≤ boundN x := by
  apply p.N_polynomial.trans
  unfold boundN
  gcongr
lemma parameters_D_le {G : GraphInput} (p : Parameters G)
    (x : ℕ) (hnx : G.n ≤ 2*x) (hN : p.N ≤ boundN x) : p.D ≤ boundD x := by
  rw [p.D_polynomial]
  unfold boundD
  gcongr
lemma parameters_S_le {G : GraphInput} [Nontrivial (Fin G.n)] (p : Parameters G)
    (x : ℕ) (hnx : G.n ≤ 2*x) (hk : p.K ≤ boundK x) (hD : p.D ≤ boundD x) (he : ⌈p.epsilon⁻¹⌉₊ ≤ x) :
    p.S ≤ boundS x := by
  apply p.S_polynomial.trans
  unfold boundS
  gcongr
lemma amplifiedBits_le_bound {G : GraphInput} [Nontrivial (Fin G.n)] (p : Parameters G) (δ : ℚ)
    (x : ℕ) (hnx : G.n ≤ 2*x) (hk : p.K ≤ boundK x) (he : ⌈p.epsilon⁻¹⌉₊ ≤ x)
    (hd : Nat.clog 2 ⌈δ⁻¹⌉₊ ≤ x) : amplifiedBits p δ ≤ boundBits x := by
  have hN:=parameters_N_le p x hnx hk
  have hD:=parameters_D_le p x hnx hN
  have hS:=parameters_S_le p x hnx hk hD he
  have hm : 1000*p.K*p.S ≤ 1000*boundK x*boundS x := by gcongr
  unfold amplifiedBits stageBits
  rw [oneBits_eq,repetitions_source]
  unfold boundBits
  exact Nat.mul_le_mul (by gcongr) (Nat.mul_le_mul hk (Nat.mul_le_mul hS (totalBitsPolynomial_mono hN hD hk hm hm)))
def inputSize (G : GraphInput) (e d : ℚ) : ℕ :=
  (encodeInput G e d).length+⌈e⁻¹⌉₊+Nat.clog 2 ⌈d⁻¹⌉₊+1
lemma inputSize_pos (G : GraphInput) (e d : ℚ) : 1 ≤ inputSize G e d := by unfold inputSize; omega
lemma scheduledBits_le {G : GraphInput} [Nontrivial (Fin G.n)] (hn : 2 ≤ G.n) (hev : Even G.n)
    (e d : ℚ) (he : 0<e) (he1 : e<1) (hsparse : G.n ≤ 2*G.edges.card) :
    amplifiedBits (parameters G hn hev e he he1) d ≤ boundBits (inputSize G e d) := by
  have hnx : G.n ≤ 2*inputSize G e d := by
    have hh:=nonzero_vertices_le_input_twice G e d hsparse
    unfold inputSize
    omega
  have hex : ⌈e⁻¹⌉₊ ≤ inputSize G e d := by unfold inputSize; omega
  exact amplifiedBits_le_bound _ d _ hnx (parameters_K_le hn hev e he he1 _ hnx hex) hex (by unfold inputSize; omega)
theorem polynomial_fair_bits : ∃ C d : ℕ, ∀ (G : GraphInput) [Nontrivial (Fin G.n)]
    (hn : 2 ≤ G.n) (hev : Even G.n) (e δ : ℚ) (he : 0<e) (he1 : e<1), G.n ≤ 2*G.edges.card →
    amplifiedBits (parameters G hn hev e he he1) δ ≤ timeBound C d G e δ := by
  obtain ⟨C,d,h⟩:=boundBits_polynomial
  refine ⟨C,d,fun G _ hn hev e δ he he1 hs=>?_⟩
  exact (scheduledBits_le hn hev e δ he he1 hs).trans (h _ (inputSize_pos G e δ))
end MatchingFPRAS.BitComplexity

namespace MatchingFPRAS.UnitRefresh
lemma pairingCount_pos_even (n : ℕ) : 0<pairingCount n → Even n := by
  induction n using Nat.twoStepInduction with
  | zero => intro _; decide
  | one => simp
  | more n ih _ =>
    intro hh
    rw [pairingCount_add_two] at hh
    have hp:0<pairingCount n := Nat.pos_of_mul_pos_left hh
    exact (ih hp).add (by decide : Even 2)
end MatchingFPRAS.UnitRefresh
namespace MatchingFPRAS
open Finset

lemma count_le_complete (G : GraphInput) : Z G≤Z (completeGraph G.n) := by
  classical
  apply card_le_card
  intro M hM
  apply (mem_perfectMatchings _ _).mpr
  have h:=(mem_perfectMatchings _ _).mp hM
  refine ⟨?_,h.2⟩
  intro e he
  exact mem_filter.mpr ⟨mem_univ _,G.increasing e (h.1 he)⟩
lemma positive_count_even (G : GraphInput) (hZ : 0<Z G) : Even G.n := by
  have hh:=lt_of_lt_of_le hZ (count_le_complete G)
  rw [GraphBridge.complete_count] at hh
  exact UnitRefresh.pairingCount_pos_even _ hh
lemma positive_nonempty_two (G : GraphInput) (hZ : 0<Z G) (hn : G.n≠0) : 2≤G.n := by
  obtain ⟨k,hk⟩:=positive_count_even G hZ
  omega
lemma empty_count_one (G : GraphInput) (hn : G.n=0) : Z G=1 := by
  classical
  have hE : G.edges=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    have hh:=e.1.isLt
    omega
  have hm : perfectMatchings G={∅} := by
    ext M
    simp only [mem_perfectMatchings,mem_singleton]
    constructor
    · intro h
      simpa only [hE,subset_empty] using h.1
    · intro h
      subst M
      refine ⟨empty_subset _,?_⟩
      intro v
      have hh:=v.isLt
      omega
  unfold Z
  rw [hm,card_singleton]
end MatchingFPRAS

namespace MatchingFPRAS.Variation
open Finset
open scoped Classical

lemma padSampler_success {A : Type*} {k B : ℕ} (h : k≤B) (f : (Fin k → Bool) → A) (P : A → Prop) :
    ((univ.filter (fun b=>P (padSampler h f b))).card:ℚ)/(2:ℚ)^B =
      ((univ.filter (fun b=>P (f b))).card:ℚ)/(2:ℚ)^k := by
  have hh:=congrArg (fun p=>event p (fun b=>P (f b))) (padSampler_law h (id : (Fin k → Bool) → (Fin k → Bool)))
  rw [event_imageLaw,event_imageLaw] at hh
  simp only [id_eq,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] at hh
  apply Rat.cast_injective (α:=ℝ)
  push_cast
  exact hh
end MatchingFPRAS.Variation

namespace MatchingFPRAS.FiniteTrial
open BitComplexity Variation Finset
open scoped Classical

lemma padded_amplified_success {G : GraphInput} [Nontrivial (Fin G.n)]
    (p : Trial.Parameters G) (δ : ℚ) (B : ℕ) (ht : amplifiedBits p δ≤B)
    (hz : 0<Z G) (hd : 0<δ) :
    ((univ.filter (fun b=>Accurate p (padSampler ht (amplifiedBitOutput p δ) b))).card:ℚ)/
        (2:ℚ)^B≥1-δ := by
  rw [padSampler_success]
  exact amplifiedBitOutput_success p hz δ hd

theorem scheduled_fair_tapes : ∃ C d : ℕ, 0<C ∧
    ∀ (G : GraphInput) [Nontrivial (Fin G.n)] (_hn : 2≤G.n) (_hev : Even G.n)
      (e δ : ℚ) (_he : 0<e) (_he1 : e<1), G.n≤2*G.edges.card →
    ∃ f : (Fin (timeBound C d G e δ) → Bool) → ℚ,
      (∀ b,0≤f b) ∧ (0<Z G → 0<δ →
        ((univ.filter (fun b=>(1-e)*(Z G:ℚ)≤f b ∧ f b≤(1+e)*(Z G:ℚ))).card:ℚ) /
          (2:ℚ)^(timeBound C d G e δ)≥1-δ) := by
  obtain ⟨C,d,h⟩:=polynomial_fair_bits
  refine ⟨C+1,d,by omega,fun G _ hn hev e δ he he1 hs=>?_⟩
  let p:=parameters G hn hev e he he1
  have ht : amplifiedBits p δ ≤ timeBound (C+1) d G e δ := by
    exact (h G hn hev e δ he he1 hs).trans (Nat.mul_le_mul_right _ (by omega))
  let f:=padSampler ht (amplifiedBitOutput p δ)
  refine ⟨f,fun b=>amplifiedBitOutput_nonneg p δ _,fun hz hd=>?_⟩
  convert padded_amplified_success p δ _ ht hz hd using 3
  congr 1
  ext b
  simp only [mem_filter,mem_univ,true_and]
  rfl
end MatchingFPRAS.FiniteTrial

end OAI
