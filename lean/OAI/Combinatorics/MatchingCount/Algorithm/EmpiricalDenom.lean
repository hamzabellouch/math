import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.SortedList

namespace OAI

namespace MatchingFPRAS.Trial
open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis BitArithmetic
open scoped Classical

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
def empiricalDenom (G : GraphInput) (K : ℕ) : ℕ := (G.n+1)^Fintype.card (SourceVertex (Fin G.n) K)
lemma empiricalDenom_pos (G : GraphInput) (K : ℕ) : 0<empiricalDenom G K := by unfold empiricalDenom; positivity
lemma ScaleState.observables_grid (hn : 0<G.n) (s : ScaleState G j) (a : SourceMarked s.activity K) :
    GridFraction (empiricalDenom G K) (observableA s.activity K a) ∧
    GridFraction (empiricalDenom G K) (observableD s.activity s.nextActivity K a) ∧
    ∀ e₀,GridFraction (empiricalDenom G K) (observableProbe s.activity s.nextActivity K e₀ a) := by
  have h := s.observable_power a
  refine ⟨?_,?_,?_⟩
  · rcases h.1 with he|he
    · rw [he]; exact GridFraction.zero _
    · rw [he]; exact GridFraction.one (empiricalDenom_pos G K)
  · rcases h.2.1 with he|⟨t,ht,he⟩
    · rw [he]; exact GridFraction.zero _
    · rw [he,cooling_fraction G.n hn]
      exact GridFraction.cooling_power G.n _ t ht
  · intro e₀
    rcases h.2.2 e₀ with he|⟨t,ht,he⟩
    · rw [he]; exact GridFraction.zero _
    · rw [he,cooling_fraction G.n hn]
      exact GridFraction.cooling_power G.n _ t ht
lemma ScaleState.means_bits (hn : 0<G.n) (s : ScaleState G j)
    (hS : 0<S) (x : Fin S → SourceMarked s.activity K) :
    FractionBound (S*empiricalDenom G K) (sampleAverage (observableA s.activity K) x) ∧
    FractionBound (S*empiricalDenom G K) (sampleAverage (observableD s.activity s.nextActivity K) x) ∧
    ∀ e₀,FractionBound (S*empiricalDenom G K) (sampleAverage (observableProbe s.activity s.nextActivity K e₀) x) := by
  have hpos := Nat.mul_pos hS (empiricalDenom_pos G K)
  refine ⟨?_,?_,?_⟩
  · exact (GridFraction.average _ x (fun i=>(s.observables_grid hn (x i)).1)).fractionBound hpos
  · exact (GridFraction.average _ x (fun i=>(s.observables_grid hn (x i)).2.1)).fractionBound hpos
  · intro e₀
    exact (GridFraction.average _ x (fun i=>(s.observables_grid hn (x i)).2.2 e₀)).fractionBound hpos
end MatchingFPRAS.Trial

namespace MatchingFPRAS.BitArithmetic
open Finset

lemma alpha_bits : FractionBound 100000 RealStage.alpha := by
  exact ⟨1,100000,by norm_num,by norm_num,le_rfl,by norm_num [RealStage.alpha]⟩
def matrixBound (D B : ℕ) : ℕ := 200000*(D+1)*B^2
lemma matrixBound_large (D B : ℕ) (hB : 1≤B) : 100000 ≤ matrixBound D B := by
  unfold matrixBound
  have hb2 : 1≤B^2 := one_le_pow₀ hB
  nlinarith
lemma ratioEstimate_bits {B : ℕ} {a d : ℝ} (hB : 1≤B)
    (ha : FractionBound B a) (hd : FractionBound B d) :
    FractionBound (B^2) (RealStage.ratioEstimate a d) := by
  unfold RealStage.ratioEstimate
  split_ifs with h
  · simpa [pow_two] using hd.div ha h
  · exact FractionBound.one (one_le_pow₀ hB)
lemma upperEstimate_bits (D : ℕ) {B : ℕ} {d z : ℝ} (hB : 1≤B)
    (hd : FractionBound B d) (hz : FractionBound B z) :
    FractionBound (matrixBound D B) (RealStage.upperEstimate D d z) := by
  have hlarge := matrixBound_large D B hB
  unfold RealStage.upperEstimate
  split_ifs with h
  · have ht : FractionBound (matrixBound D B) ((D:ℝ)*z/d+RealStage.alpha) := by
      convert (((FractionBound.nat D).mul hz).div hd h).add alpha_bits using 1
      unfold matrixBound
      ring
    exact (alpha_bits.mono hlarge).max
      ((FractionBound.nat 3 |>.mono (by omega)).min ht)
  · exact FractionBound.one (by omega)
lemma scalingTrace_bits {n : ℕ} (hn : 2≤n) (G : Fin n → Fin n → ℝ)
    (hsym : ∀ i j,G i j=G j i) (hG : ∀ i j,i≠j → RealStage.alpha≤G i j ∧ G i j≤3)
    (B : ℕ) (hB : 2≤B) (hb : ∀ i j,FractionBound B (G i j)) (k : ℕ) :
    ∀ i,FractionBound (B^(k+1)) (RealStage.scalingTrace hn G k i) := by
  have hB1 : 1≤B := by omega
  induction k with
  | zero =>
    intro i
    change FractionBound (B^(0+1)) 2
    simpa using (show FractionBound B (2:ℝ) from ⟨2,1,by omega,hB,hB1,by norm_num⟩)
  | succ k ih =>
    intro i
    have hmono : B^(k+1)≤B^(k+1+1) := Nat.pow_le_pow_right hB1 (by omega)
    dsimp only [RealStage.scalingTrace]
    split_ifs with hk
    · unfold RealStage.scaleUpdate
      by_cases hi : i=⟨k,hk⟩
      · subst i
        simp only [Function.update_self]
        unfold RealStage.rowMaximum
        have hpos := (RealStage.scalingTrace_invariant hn G hsym hG k).1.pos
        convert FractionBound.sup' (univ.erase (⟨k,hk⟩ : Fin n)) (RealStage.others_nonempty hn _)
          (fun j=>G ⟨k,hk⟩ j / RealStage.scalingTrace hn G k j) (B*B^(k+1))
          (fun j _=>(hb ⟨k,hk⟩ j).div (ih j) (hpos j)) using 1
        rw [pow_succ,Nat.mul_comm]
      · rw [Function.update_of_ne hi]
        exact (ih i).mono hmono
    · exact (ih i).mono hmono
end MatchingFPRAS.BitArithmetic

namespace MatchingFPRAS.Trial
open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis BitArithmetic
open scoped Classical

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
lemma ScaleState.ratioEstimate_bits (hn : 0<G.n) (s : ScaleState G j)
    (hS : 0<S) (x : Fin S → SourceMarked s.activity K) :
    FractionBound ((S*empiricalDenom G K)^2) (s.ratioEstimate x) := by
  have hb := s.means_bits hn hS x
  exact BitArithmetic.ratioEstimate_bits (Nat.mul_pos hS (empiricalDenom_pos G K)) hb.1 hb.2.1
lemma ScaleState.matrix_bits (hn : 0<G.n) (s : ScaleState G j)
    (hS : 0<S) (x : Fin S → SourceMarked s.activity K) (a b : Fin G.n) :
    FractionBound (matrixBound (sourceD (V:=Fin G.n) K) (S*empiricalDenom G K)) (s.matrix x a b) := by
  have hb := s.means_bits hn hS x
  unfold ScaleState.matrix estimateMatrix
  apply upperEstimate_bits _ (Nat.mul_pos hS (empiricalDenom_pos G K)) hb.2.1
  unfold probeMatrix
  split_ifs
  · exact FractionBound.zero (Nat.mul_pos hS (empiricalDenom_pos G K))
  · exact hb.2.2 _
lemma ScaleState.updateVector_bits (hn : 2≤G.n) (s : ScaleState G j)
    (hS : 0<S) (x : Fin S → SourceMarked s.activity K) (a : Fin G.n) :
    FractionBound ((matrixBound (sourceD (V:=Fin G.n) K) (S*empiricalDenom G K))^(G.n+1)) (s.updateVector hn x a) := by
  apply scalingTrace_bits hn (s.matrix x) (estimateMatrix_symm _ _ _)
    (fun a b _=>s.matrix_bounds x a b) _ _ (fun a b=>s.matrix_bits (by omega) hS x a b)
  have hh := matrixBound_large (sourceD (V:=Fin G.n) K) (S*empiricalDenom G K)
    (Nat.mul_pos hS (empiricalDenom_pos G K))
  omega
open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis BitArithmetic
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
omit [Nontrivial (Fin G.n)] in
lemma initial_scale_bits (hn : 2≤G.n) (a : Fin G.n) :
    FractionBound (G.n+1) ((initialScaleState G hn).scale a) := by
  refine ⟨1,Nat.sqrt (G.n-1),?_,by omega,?_,?_⟩
  · exact Nat.le_sqrt.mpr (by omega)
  · exact (Nat.sqrt_le_self _).trans (by omega)
  · change (Initializer.initialScale G.n:ℝ)=_
    simp [Initializer.initialScale]

noncomputable def Parameters.empiricalBound (p : Parameters G) : ℕ := p.S*empiricalDenom G p.K
noncomputable def Parameters.matrixBound (p : Parameters G) : ℕ := BitArithmetic.matrixBound p.D p.empiricalBound
lemma Parameters.empiricalBound_pos (p : Parameters G) : 0<p.empiricalBound :=
  Nat.mul_pos p.S_pos (empiricalDenom_pos G p.K)
lemma Parameters.matrixBound_large (p : Parameters G) : 100000≤p.matrixBound :=
  BitArithmetic.matrixBound_large p.D p.empiricalBound p.empiricalBound_pos
noncomputable def Parameters.scaleBound (p : Parameters G) (j : ℕ) : ℕ :=
  (G.n+1)*p.matrixBound^(j*(G.n+1))
lemma layers_scale_bits (p : Parameters G) (j : ℕ) (hj : j≤p.K)
    (x : (layers p j hj).Ω) (a : Fin G.n) :
    FractionBound (p.scaleBound j) ((layers p j hj).state x |>.scale a) := by
  induction j with
  | zero => simpa [layers,firstLayer,Parameters.scaleBound] using initial_scale_bits p.hn a
  | succ j ih =>
    change FractionBound _ (((layers p j (by omega)).state x.1).scale a *
      ((layers p j (by omega)).state x.1).updateVector p.hn x.2 a)
    have hv := ((layers p j (by omega)).state x.1).updateVector_bits p.hn p.S_pos x.2 a
    have hh := (ih (by omega) x.1).mul hv
    convert hh using 1
    change (G.n+1)*p.matrixBound^((j+1)*(G.n+1))=
      ((G.n+1)*p.matrixBound^(j*(G.n+1)))*p.matrixBound^(G.n+1)
    rw [add_mul, one_mul, pow_add]
    ring
lemma layers_ratio_bits (p : Parameters G) (j : ℕ) (hj : j≤p.K)
    (x : (layers p j hj).Ω) (i : Fin j) :
    FractionBound (p.empiricalBound^2) ((layers p j hj).ratios x i) := by
  induction j with
  | zero => exact Fin.elim0 i
  | succ j ih =>
    refine Fin.lastCases ?_ (fun i=>?_) i
    · simpa only [layers,Layer.append,Fin.snoc_last,Parameters.empiricalBound] using
        ((layers p j (by omega)).state x.1).ratioEstimate_bits (by have := p.hn; omega) p.S_pos x.2
    · simpa only [layers,Layer.append,Fin.snoc_castSucc] using ih (by omega) x.1 i
lemma output_bits (p : Parameters G) (x : (layers p p.K le_rfl).Ω) :
    FractionBound ((Z (completeGraph G.n)+1)*(p.empiricalBound^2)^p.K) (output p x) := by
  have h := FractionBound.prod univ ((layers p p.K le_rfl).ratios x) (p.empiricalBound^2)
    (fun i _=>layers_ratio_bits p p.K le_rfl x i)
  simpa [output] using (FractionBound.nat (Z (completeGraph G.n))).mul h

noncomputable def rationalOutput (p : Parameters G) (x : (layers p p.K le_rfl).Ω) : ℚ :=
  (output_bits p x).choose / (output_bits p x).choose_spec.choose
lemma rationalOutput_cast (p : Parameters G) (x : (layers p p.K le_rfl).Ω) :
    (rationalOutput p x:ℝ)=output p x := by
  have h := (output_bits p x).choose_spec.choose_spec.2.2.2
  simpa [rationalOutput] using h.symm
lemma rationalOutput_nonneg (p : Parameters G) (x : (layers p p.K le_rfl).Ω) :
    0≤rationalOutput p x := by
  exact_mod_cast (show (0:ℝ)≤(rationalOutput p x:ℝ) by rw [rationalOutput_cast]; exact output_nonneg p x)
lemma rationalOutput_accurate (p : Parameters G) (x : (layers p p.K le_rfl).Ω) :
    Accurate p (output p x) ↔
      (1-p.epsilon)*(Z G:ℚ)≤rationalOutput p x ∧ rationalOutput p x≤(1+p.epsilon)*(Z G:ℚ) := by
  rw [← rationalOutput_cast p x]
  unfold Accurate
  norm_cast
end MatchingFPRAS.Trial

namespace MatchingFPRAS.FiniteTrial
open Finset Enlargement Transport BitArithmetic
open scoped Classical

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K) := Fintype.ofFinite _
lemma ScaleState.ratioEstimate_bits (hn : 0<G.n) (s : ScaleState G j) (hS : 0<S)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) :
    FractionBound ((S*Trial.empiricalDenom G K)^2)
      (s.ratioEstimate (RationalSource.sourceMarkedEquiv s.activity K ∘ x):ℝ) := by
  have hb := s.toReal.ratioEstimate_bits (K:=K) (S:=S) hn hS
  unfold Trial.ScaleState.ratioEstimate at hb
  rw [←s.activity_cast,←s.nextActivity_cast] at hb
  rw [s.ratioEstimate_cast]
  exact hb x
lemma ScaleState.matrix_bits (hn : 0<G.n) (s : ScaleState G j) (hS : 0<S)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) (a b : Fin G.n) :
    FractionBound (matrixBound (Enlargement.sourceD (V:=Fin G.n) K) (S*Trial.empiricalDenom G K))
      (s.matrix (RationalSource.sourceMarkedEquiv s.activity K ∘ x) a b:ℝ) := by
  have hb := s.toReal.matrix_bits (K:=K) (S:=S) hn hS
  unfold Trial.ScaleState.matrix at hb
  rw [←s.activity_cast,←s.nextActivity_cast] at hb
  have he := congrFun (congrFun (s.matrix_cast x) a) b
  rw [he,sourceD_eq]
  exact hb x a b
lemma ScaleState.updateVector_bits (hn : 2≤G.n) (s : ScaleState G j) (hS : 0<S)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) (a : Fin G.n) :
    FractionBound ((matrixBound (Enlargement.sourceD (V:=Fin G.n) K) (S*Trial.empiricalDenom G K))^(G.n+1))
      (s.updateVector hn (RationalSource.sourceMarkedEquiv s.activity K ∘ x) a:ℝ) := by
  rw [ScaleState.updateVector,Counting.scalingTrace_cast]
  apply scalingTrace_bits hn _ _ _ _ _ _ _ a
  · intro a b
    exact_mod_cast s.matrix_symm _ a b
  · intro a b _
    have h:=s.matrix_bounds (RationalSource.sourceMarkedEquiv s.activity K ∘ x) a b
    constructor
    · have hh : ((Counting.alpha:ℚ):ℝ) ≤ (s.matrix (RationalSource.sourceMarkedEquiv s.activity K ∘ x) a b:ℝ) := by exact_mod_cast h.1
      simpa [Counting.alpha,RealStage.alpha] using hh
    · exact_mod_cast h.2
  · have h:=matrixBound_large (Enlargement.sourceD (V:=Fin G.n) K) (S*Trial.empiricalDenom G K)
      (Nat.mul_pos hS (Trial.empiricalDenom_pos G K))
    omega
  · intro a b
    exact s.matrix_bits (by omega) hS x a b
omit [Nontrivial (Fin G.n)] in
lemma initial_scale_bits (hn : 2≤G.n) (a : Fin G.n) :
    FractionBound (G.n+1) ((initialScaleState G hn).scale a:ℝ) := by
  exact Trial.initial_scale_bits hn a
lemma layers_scale_bits (p : Trial.Parameters G) (j : ℕ) (hj : j≤p.K)
    (x : (layers p j hj).Ω) (a : Fin G.n) :
    FractionBound (p.scaleBound j) ((layers p j hj).state x |>.scale a:ℝ) := by
  induction j with
  | zero => simpa [layers,firstLayer,Trial.Parameters.scaleBound] using initial_scale_bits p.hn a
  | succ j ih =>
    change FractionBound _ ((((layers p j (by omega)).state x.1).scale a *
      ((layers p j (by omega)).state x.1).updateVector p.hn
        (RationalSource.sourceMarkedEquiv ((layers p j (by omega)).state x.1).activity p.K ∘ x.2) a:ℚ):ℝ)
    rw [Rat.cast_mul]
    have hv := ((layers p j (by omega)).state x.1).updateVector_bits p.hn p.S_pos x.2 a
    have hh := (ih (by omega) x.1).mul hv
    convert hh using 1
    change (G.n+1)*p.matrixBound^((j+1)*(G.n+1))=
      ((G.n+1)*p.matrixBound^(j*(G.n+1)))*p.matrixBound^(G.n+1)
    rw [add_mul,one_mul,pow_add]
    ring
lemma layers_ratio_bits (p : Trial.Parameters G) (j : ℕ) (hj : j≤p.K)
    (x : (layers p j hj).Ω) (i : Fin j) :
    FractionBound (p.empiricalBound^2) ((layers p j hj).ratios x i:ℝ) := by
  induction j with
  | zero => exact Fin.elim0 i
  | succ j ih =>
    refine Fin.lastCases ?_ (fun i=>?_) i
    · simpa only [layers,Layer.append,Fin.snoc_last,Trial.Parameters.empiricalBound] using
        ((layers p j (by omega)).state x.1).ratioEstimate_bits (by have := p.hn; omega) p.S_pos x.2
    · simpa only [layers,Layer.append,Fin.snoc_castSucc] using ih (by omega) x.1 i
lemma output_bits (p : Trial.Parameters G) (x : (layers p p.K le_rfl).Ω) :
    FractionBound ((Z (completeGraph G.n)+1)*(p.empiricalBound^2)^p.K) (output p x:ℝ) := by
  have h := FractionBound.prod univ (fun i=>((layers p p.K le_rfl).ratios x i:ℝ)) (p.empiricalBound^2)
    (fun i _=>layers_ratio_bits p p.K le_rfl x i)
  simpa [output,Rat.cast_mul,Rat.cast_prod] using (FractionBound.nat (Z (completeGraph G.n))).mul h
end MatchingFPRAS.FiniteTrial

namespace MatchingFPRAS.BitArithmetic
lemma FractionBound.num_den {B : ℕ} {q : ℚ} (h : FractionBound B (q:ℝ)) :
    q.num.natAbs≤B ∧ q.den≤B := by
  obtain ⟨a,b,hb,ha,hbb,he⟩:=h
  have hq : q=(a:ℚ)/b := by
    apply Rat.cast_injective (α:=ℝ)
    simpa only [Rat.cast_div,Rat.cast_natCast] using he
  have hq' : q=Rat.divInt (a:ℤ) (b:ℤ) := by simpa only [Rat.divInt_eq_div,Int.cast_natCast] using hq
  have hb0 : (b:ℤ)≠0 := by exact_mod_cast hb.ne'
  have hd : q.den∣b := by
    have hh:=Rat.den_dvd (a:ℤ) (b:ℤ)
    rw [←hq'] at hh
    exact_mod_cast hh
  refine ⟨?_,(Nat.le_of_dvd hb hd).trans hbb⟩
  by_cases ha0 : a=0
  · simp [ha0] at hq
    simp [hq]
  · have hh:=Rat.num_dvd (a:ℤ) hb0
    rw [←hq'] at hh
    have hn : q.num.natAbs∣a := by simpa using Int.natAbs_dvd_natAbs.mpr hh
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hn).trans ha
lemma size_mul_le (a b : ℕ) : (a*b).size≤a.size+b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  have h₁:=Nat.lt_size_self a
  have h₂:=Nat.lt_size_self b
  have h₃ : 0<(2:ℕ)^a.size := by positivity
  nlinarith
lemma size_pow_le (a k : ℕ) : (a^k).size≤k*a.size+1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h:=size_mul_le (a^k) a
    rw [Nat.succ_mul]
    omega
lemma FractionBound.encode_length {B : ℕ} {q : ℚ} (h : FractionBound B (q:ℝ)) :
    (encodeRat q).length≤2*B.size+3 := by
  have hd:=h.num_den
  have hn:=Nat.size_le_size hd.1
  have hb:=Nat.size_le_size hd.2
  have he : (encodeRat q).length=q.num.natAbs.size+q.den.size+3 := by
    unfold encodeRat encodeInt encodeNat
    split_ifs <;> simp [Nat.size_eq_bits_len] <;> omega
  rw [he]
  omega
lemma size_empiricalBound {G : GraphInput} (p : Trial.Parameters G) :
    p.empiricalBound.size≤p.S.size+Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K)*(G.n+1).size+1 := by
  unfold Trial.Parameters.empiricalBound Trial.empiricalDenom
  exact (size_mul_le _ _).trans (by have h:=size_pow_le (G.n+1) (Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K)); omega)
lemma size_matrixBound {G : GraphInput} (p : Trial.Parameters G) :
    p.matrixBound.size≤19+(p.D+1).size+2*p.empiricalBound.size := by
  unfold Trial.Parameters.matrixBound matrixBound
  have h₁:=size_mul_le (200000*(p.D+1)) (p.empiricalBound^2)
  have h₂:=size_mul_le 200000 (p.D+1)
  have h₃:=size_pow_le p.empiricalBound 2
  have h₄ : (200000:ℕ).size=18 := by decide
  omega
lemma size_scaleBound {G : GraphInput} (p : Trial.Parameters G) (j : ℕ) :
    (p.scaleBound j).size≤(G.n+1).size+j*(G.n+1)*p.matrixBound.size+1 := by
  unfold Trial.Parameters.scaleBound
  have h₁:=size_mul_le (G.n+1) (p.matrixBound^(j*(G.n+1)))
  have h₂:=size_pow_le p.matrixBound (j*(G.n+1))
  omega
end MatchingFPRAS.BitArithmetic
namespace MatchingFPRAS.FiniteTrial
open BitArithmetic

variable {G : GraphInput} [Nontrivial (Fin G.n)]
lemma scale_encode_length (p : Trial.Parameters G) (j : ℕ) (hj : j≤p.K)
    (x : (layers p j hj).Ω) (a : Fin G.n) :
    (encodeRat (((layers p j hj).state x).scale a)).length ≤
      2*((G.n+1).size+j*(G.n+1)*(19+(p.D+1).size+2*(p.S.size+
        Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K)*(G.n+1).size+1))+1)+3 := by
  have h₁:=(layers_scale_bits p j hj x a).encode_length
  have h₂:=size_scaleBound p j
  have h₃:=size_matrixBound p
  have h₄:=size_empiricalBound p
  have hb : (p.scaleBound j).size≤
      (G.n+1).size+j*(G.n+1)*(19+(p.D+1).size+2*(p.S.size+
        Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K)*(G.n+1).size+1))+1 := by
    calc
      _ ≤ (G.n+1).size+j*(G.n+1)*p.matrixBound.size+1 := h₂
      _ ≤ (G.n+1).size+j*(G.n+1)*(19+(p.D+1).size+2*p.empiricalBound.size)+1 := by gcongr
      _ ≤ _ := by gcongr
  omega
end MatchingFPRAS.FiniteTrial

namespace MatchingFPRAS.Counting

def schedulePolynomial (n : ℕ) (e : ℚ) : ℕ := n*(n*n+32*⌈e⁻¹⌉₊)
lemma polynomial_schedule (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) :
    scheduleAdmissible n e (schedulePolynomial n e) := by
  have hn0 : (0:ℚ)<n := by exact_mod_cast (show 0<n by omega)
  have hnz : (n:ℚ)≠0 := ne_of_gt hn0
  have hb : (2:ℚ)≤(1+1/n)^n := by
    have hh:=one_add_mul_le_pow (a:=(1/(n:ℚ))) (le_trans (by norm_num : (-2:ℚ)≤0) (by positivity : (0:ℚ)≤1/n)) n
    norm_num [mul_inv_cancel₀ hnz] at hh
    simpa only [one_div] using hh
  have hec : e⁻¹≤(⌈e⁻¹⌉₊:ℚ) := Nat.le_ceil _
  have hecp : 0<⌈e⁻¹⌉₊ := by
    by_contra h
    have hz : ⌈e⁻¹⌉₊=0 := by omega
    rw [hz] at hec
    have hp : 0<e⁻¹ := inv_pos.mpr he
    norm_num at hec
    linarith
  have hnp : (n:ℚ)≤2^n := by exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hp₁ : (n:ℚ)^(n/2)≤2^(n*n) := by
    calc
      _ ≤ (2^n:ℚ)^(n/2) := pow_le_pow_left₀ hn0.le hnp _
      _ = (2:ℚ)^(n*(n/2)) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left n (Nat.div_le_self _ _))
  have hp₂ : (32:ℚ)/e≤2^(32*⌈e⁻¹⌉₊) := by
    calc
      _ = 32*e⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 32*(⌈e⁻¹⌉₊:ℚ) := mul_le_mul_of_nonneg_left hec (by norm_num)
      _ ≤ (2:ℚ)^(32*⌈e⁻¹⌉₊) := by exact_mod_cast (Nat.lt_two_pow_self (n:=32*⌈e⁻¹⌉₊)).le
  have hp : (n:ℚ)^(n/2)*(32/e) ≤ (1+1/n)^schedulePolynomial n e := by
    calc
      _ ≤ (2:ℚ)^(n*n)*2^(32*⌈e⁻¹⌉₊) := mul_le_mul hp₁ hp₂ (by positivity) (by positivity)
      _ = (2:ℚ)^(n*n+32*⌈e⁻¹⌉₊) := (pow_add _ _ _).symm
      _ ≤ ((1+1/n:ℚ)^n)^(n*n+32*⌈e⁻¹⌉₊) := pow_le_pow_left₀ (by norm_num) hb _
      _ = _ := by rw [←pow_mul]; rfl
  refine ⟨by unfold schedulePolynomial; have := Nat.mul_pos (show 0<n by omega) (show 0<n*n+32*⌈e⁻¹⌉₊ by positivity); omega,?_⟩
  have hbase : (0:ℚ)<1+1/n := by positivity
  apply (div_le_iff₀ (pow_pos hbase _)).mpr
  have hh := (div_le_iff₀ he).mp (show (n:ℚ)^(n/2)*32/e≤(1+1/n)^schedulePolynomial n e by simpa [mul_div_assoc] using hp)
  nlinarith
lemma leastSchedule_polynomial (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) (he1 : e<1) :
    leastSchedule n hn e he he1 ≤ schedulePolynomial n e :=
  leastSchedule_le n hn e he he1 _ (polynomial_schedule n hn e he)
end MatchingFPRAS.Counting

end OAI
