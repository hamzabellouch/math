import Mathlib
import OAI.Probability.LogConcave.TensorGraphs.PrimaryPositionTensor
import OAI.Probability.LogConcave.TensorGraphs.ColoringSplit

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory GraphSchedule
open scoped BigOperators Classical NNReal

variable {n d : ℕ}
local instance cutDecEqCB (β : Fin n → ℕ) (q : ℕ) :
    DecidableEq (InternalEdge β ⊕ Fin q) :=
  @instDecidableEqSum _ _ (Classical.decEq _) (Classical.decEq _)

def onChain (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) : TraceEdge β q → Prop
  | Sum.inl e => e.1.castSucc=i ∨ e.1.succ=i
  | Sum.inr (Sum.inl _) => 0=i
  | Sum.inr (Sum.inr _) => Fin.last n=i

abbrev ChainSlot (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) :=
  {t : TraceEdge β q // onChain β q i t}

lemma onChain_iff_incident {S : State (Fin (n+1))}
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) (t : TraceEdge β q) :
    onChain β q i t ↔ IncidentAt (edgeSource (S:=S) β) (edgeTarget hS β)
      (Sum.inl 0) (Sum.inl (Fin.last n)) (Sum.inl i) q (traceEmbed β q t) := by
  rcases t with e | (j | j) <;>
    simp only [onChain, traceEmbed, IncidentAt, edgeSource, edgeTarget, Sum.inl.injEq]

def chainSlotEquiv {S : State (Fin (n+1))}
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (i : Fin (n+1)) :
    ChainSlot β q i ≃ PrimaryTraceSlot hS β q i where
  toFun t := ⟨t.val,(onChain_iff_incident hS β q i t.val).mp t.property⟩
  invFun t := ⟨t.val,(onChain_iff_incident hS β q i t.val).mpr t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def closeTrace (β : Fin n → ℕ) (q : ℕ) :
    TraceEdge β q → ((k : Fin n) × Fin (β k)) ⊕ Fin q
  | Sum.inl e => Sum.inl e
  | Sum.inr (Sum.inl j) => Sum.inr j
  | Sum.inr (Sum.inr j) => Sum.inr j

abbrev TraceColors (β : Fin n → ℕ) (q d : ℕ) :=
  (((k : Fin n) × Fin (β k)) ⊕ Fin q) → Fin d

abbrev FullColors (β : Fin n → ℕ) (q d : ℕ) :=
  InternalEdge β ⊕ Fin q → Fin d

def chainField (β : Fin n → ℕ) (q : ℕ)
    (F : ∀i,(ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    (t : TraceColors β q d) (i : Fin (n+1)) (z : Fin d) : Point d → ℝ :=
  F i (fun u => t (closeTrace β q u.val)) z

def chainBranch (β : Fin n → ℕ) (q : ℕ) (H : Point d → ℝ) (b : Fin d → Point d)
    (F : ∀i,(ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    (S : State (Fin (n+1))) (x : Point d) : ℝ :=
  ∑c : FullColors β q d,
    (∏i,JetCalculus.jet (fun j => b (c (Sum.inl (Sum.inr j)))) (S.derivatives i)
      (F i (fun u => duplicate c (traceEmbed β q u.val)) (c (Sum.inl (Sum.inr i)))) x)*
    (S.hessians.map (fun h => hessian H (fun j => b (c (Sum.inl (Sum.inr j)))) h x)).prod

lemma split_duplicate (β : Fin n → ℕ) (q : ℕ) (t : TraceColors β q d)
    (a : Fin (n+1) → Fin d) (u : TraceEdge β q) :
    duplicate (coloringSplit.symm (t,a)) (traceEmbed β q u) = t (closeTrace β q u) := by
  rcases u with e | (j | j) <;> rfl

lemma split_adjoint (β : Fin n → ℕ) (q : ℕ) (t : TraceColors β q d)
    (a : Fin (n+1) → Fin d) (j : Fin (n+1)) :
    coloringSplit.symm (t,a) (Sum.inl (Sum.inr j)) = a j := rfl

lemma chainBranch_eq_split (β : Fin n → ℕ) (q : ℕ) (H : Point d → ℝ)
    (b : Fin d → Point d)
    (F : ∀i,(ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    (S : State (Fin (n+1))) (x : Point d) :
    chainBranch β q H b F S x = ∑t : TraceColors β q d, ∑a : Fin (n+1) → Fin d,
      (∏i,JetCalculus.jet (fun j => b (a j)) (S.derivatives i)
        (chainField β q F t i (a i)) x)*
      (S.hessians.map (fun h => hessian H (fun j => b (a j)) h x)).prod := by
  unfold chainBranch
  rw [←(Equiv.sum_comp (coloringSplit.symm :
    (TraceColors β q d × (Fin (n+1) → Fin d)) ≃ FullColors β q d))]
  rw [Fintype.sum_prod_type]
  congr 1
  funext t
  congr 1
  funext a
  simp only [split_duplicate, split_adjoint, chainField]

lemma chainBranch_polySmooth (β : Fin n → ℕ) (q : ℕ) {H : Point d → ℝ}
    (hH : PolySmooth H) (b : Fin d → Point d)
    (F : ∀i,(ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    (hF : ∀i c z,PolySmooth (F i c z)) (S : State (Fin (n+1))) :
    PolySmooth (chainBranch β q H b F S) := by
  exact PolySmooth.sum Finset.univ (fun c _ =>
    branch_factor_polySmooth S hH (fun j => b (c (Sum.inl (Sum.inr j))))
      (fun i => F i (fun u => duplicate c (traceEmbed β q u.val))
        (c (Sum.inl (Sum.inr i)))) (fun i => hF i _ _))

theorem integral_chain_expansion (β : Fin n → ℕ) (q : ℕ)
    {H : Point d → ℝ} (b : Fin d → Point d)
    (F : ∀i,(ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    {K : ℝ≥0} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    (hK : LipschitzWith K (gradient H)) (hF : ∀i c z,PolySmooth (F i c z)) :
    (∫x,(∑t : TraceColors β q d,∏i,tensorAdjoint H b (chainField β q F t i) x) ∂gibbs H) =
      ((expand (Fintype.card (Fin (n+1))) initial).map
        (fun S => ∫x,chainBranch β q H b F S x ∂gibbs H)).sum := by
  rw [parametrized_adjoint_expansion b (chainField β q F) hH ht hK
    (fun t i z => hF i _ z)]
  congr 1
  apply List.map_congr_left
  intro S _
  simp_rw [chainBranch_eq_split]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t _
    rw [integral_finsetSum]
    intro a _
    exact (branch_factor_polySmooth S hH (fun j => b (a j))
      (fun i => chainField β q F t i (a i)) (fun i => hF i _ _)).integrable
      hH.smooth.continuous ht
  · intro t _
    exact (PolySmooth.sum Finset.univ (fun a _ => branch_factor_polySmooth S hH
      (fun j => b (a j)) (fun i => chainField β q F t i (a i))
      (fun i => hF i _ _))).integrable hH.smooth.continuous ht

open TensorEnergy
open scoped ENNReal

def chainPositionTensor (β : Fin n → ℕ) (q : ℕ) (b : Fin d → Point d)
    (i : Fin (n+1))
    (F : (ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    (j : ℕ) (x : Point d)
    (a : ChainSlot β q i ⊕ (Unit ⊕ Fin j) → Fin d) : ℝ :=
  JetCalculus.jet (fun k => b (a (Sum.inr (Sum.inr k)))) (List.finRange j)
    (F (fun t => a (Sum.inl t)) (a (Sum.inr (Sum.inl ())))) x

lemma primaryPositionTensor_of_chain {S : State (Fin (n+1))}
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (q : ℕ) (b : Fin d → Point d) (i : Fin (n+1))
    (F : (ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    (x : Point d) (M : ℝ)
    (hM : AllSplitBound (chainPositionTensor β q b i F (S.derivatives i).length x) M) :
    AllSplitBound (primaryPositionTensor hS β q b i
      (fun a z => F (a ∘ chainSlotEquiv hS β q i) z) x) M := by
  exact hM.reindex ((chainSlotEquiv hS β q i).sumCongr
    (Equiv.refl (Unit ⊕ Fin (S.derivatives i).length)))

theorem chain_branch_bound {S : State (Fin (n+1))}
    (μ : Measure (Point d))
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (β : Fin n → ℕ) (hβ : ∀k,0<β k) (q : ℕ) (hq : 0<q)
    (H : Point d → ℝ) (b : Fin d → Point d)
    (F : ∀i,(ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    (Mp : Fin (n+1) → Point d → ℝ) (Mh : S.hessians → Point d → ℝ)
    (hMp0 : ∀i x,0≤Mp i x) (hMh0 : ∀h x,0≤Mh h x)
    (hTp : ∀i x,AllSplitBound
      (chainPositionTensor β q b i (F i) (S.derivatives i).length x) (Mp i x))
    (hTh : ∀(h : S.hessians) x,AllSplitBound
      (hessianPositionTensor H b (h : Hessian (Fin (n+1))) x) (Mh h x))
    (j k : ℕ) (A R : ℝ≥0∞) (hA : 1≤A) (hR : 1≤R) (hAf : A≠⊤) (hRf : R≠⊤)
    (hMp : ∀i,AEMeasurable (fun x => ENNReal.ofReal (Mp i x)) μ)
    (hp : ∀i,(∫⁻x,ENNReal.ofReal (Mp i x)^(n+1) ∂μ)≤
      (A^(j+(S.derivatives i).length+1)*R^(k+j+(S.derivatives i).length))^(n+1))
    (hh : ∀(h : S.hessians) x,ENNReal.ofReal (Mh h x)≤
      A^((h : Hessian (Fin (n+1))).extra.length+1)*R^((h : Hessian (Fin (n+1))).extra.length)) :
    (∫⁻x,ENNReal.ofReal |chainBranch β q H b F S x| ∂μ)≤
      (d:ℝ≥0∞)^q*(A^(2*(n+1)*(j+1))*R^((n+1)*(k+j+1))) := by
  let G : ∀i,(PrimaryTraceSlot hS β q i → Fin d) → Fin d → Point d → ℝ :=
    fun i a z => F i (a ∘ chainSlotEquiv hS β q i) z
  have hG : ∀i x,AllSplitBound (primaryPositionTensor hS β q b i (G i) x) (Mp i x) :=
    fun i x => primaryPositionTensor_of_chain hS β q b i (F i) x (Mp i x) (hTp i x)
  have hb := quantitative_branch_integral_bound μ hS β hβ q hq H b G Mp Mh hMp0 hMh0
    hG hTh j k A R hA hR hAf hRf hMp hp hh
  simpa only [G,Function.comp_def,chainSlotEquiv,Equiv.coe_fn_mk,chainBranch] using hb

theorem integral_chain_bound (β : Fin n → ℕ) (q : ℕ)
    {H : Point d → ℝ} (b : Fin d → Point d)
    (F : ∀i,(ChainSlot β q i → Fin d) → Fin d → Point d → ℝ)
    {K : ℝ≥0} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    (hK : LipschitzWith K (gradient H)) (hF : ∀i c z,PolySmooth (F i c z))
    (B : ℝ≥0∞)
    (hB : ∀S∈expand (Fintype.card (Fin (n+1))) initial,
      (∫⁻x,ENNReal.ofReal |chainBranch β q H b F S x| ∂gibbs H)≤B) :
    ENNReal.ofReal |∫x,(∑t : TraceColors β q d,∏i,tensorAdjoint H b
      (chainField β q F t i) x) ∂gibbs H| ≤ ((3*(n+1)+1:ℕ):ℝ≥0∞)^(n+1)*B := by
  rw [integral_chain_expansion β q b F hH ht hK hF]
  have hi (S : State (Fin (n+1))) :
      Integrable (chainBranch β q H b F S) (gibbs H) :=
    (chainBranch_polySmooth β q hH b F hF S).integrable hH.smooth.continuous ht
  have hiL (L : List (State (Fin (n+1)))) :
      Integrable (fun x => (L.map (fun S => chainBranch β q H b F S x)).sum) (gibbs H) := by
    induction L with
    | nil => simp
    | cons S L ih =>
      change Integrable (fun x => chainBranch β q H b F S x+
        (L.map (fun S => chainBranch β q H b F S x)).sum) (gibbs H)
      exact (hi S).add ih
  have he (L : List (State (Fin (n+1)))) :
      (L.map (fun S => ∫x,chainBranch β q H b F S x ∂gibbs H)).sum =
      ∫x,(L.map (fun S => chainBranch β q H b F S x)).sum ∂gibbs H := by
    induction L with
    | nil => simp
    | cons S L ih => simp only [List.map_cons,List.sum_cons,integral_add (hi S) (hiL L),ih]
  rw [he]
  have hb := removal_sum_bound (gibbs H) (chainBranch β q H b F) B
    (fun S _ => (hi S).aestronglyMeasurable.aemeasurable) hB
  apply le_trans _ (by simpa only [Fintype.card_fin] using hb)
  simpa only [Real.enorm_eq_ofReal_abs,Fintype.card_fin] using
    enorm_integral_le_lintegral_enorm (μ:=gibbs H)
      (fun x => ((expand (Fintype.card (Fin (n+1))) initial).map
        (fun S => chainBranch β q H b F S x)).sum)

end LogConcaveSampling.AdjointRemoval

end

end

section

noncomputable section
namespace LogConcaveSampling.CycleTrace
open scoped BigOperators

abbrev Primary (s : ℕ) := Fin ((2*s+1)+1)

def primaryPair (s : ℕ) : (Fin (s+1) × Fin 2) ≃ Primary s :=
  finProdFinEquiv.trans (finCongr (by omega))

@[simp] lemma primaryPair_val (s : ℕ) (t : Fin (s+1)) (z : Fin 2) :
    (primaryPair s (t,z)).val = 2*t.val+z.val := by
  simp [primaryPair,finProdFinEquiv,add_comm]

def bundle {s : ℕ} (a b : ℕ) (k : Fin (2*s+1)) : ℕ :=
  if k.val%2=0 then b else a

abbrev Wire (s a b : ℕ) := ((k : Fin (2*s+1)) × Fin (bundle a b k)) ⊕ Fin a
abbrev CycleWire (s a b : ℕ) := (Fin (s+1) × Fin a) ⊕ (Fin (s+1) × Fin b)

lemma row_index_lt {s : ℕ} (t : Fin (s+1)) (_ht : t.val≠0) : 2*t.val-1<2*s+1 := by
  omega
lemma row_index_odd {s : ℕ} (t : Fin (s+1)) (ht : t.val≠0) : (2*t.val-1)%2≠0 := by
  omega
lemma col_index_lt {s : ℕ} (t : Fin (s+1)) : 2*t.val<2*s+1 := by omega

lemma row_bundle {s : ℕ} (a b : ℕ) (t : Fin (s+1)) (ht : t.val≠0) :
    bundle a b ⟨2*t.val-1,row_index_lt t ht⟩ = a := by
  simp only [bundle, row_index_odd t ht, ite_false]
lemma col_bundle {s : ℕ} (a b : ℕ) (t : Fin (s+1)) :
    bundle a b ⟨2*t.val,col_index_lt t⟩ = b := by simp [bundle]

def encodeWire {s a b : ℕ} : CycleWire s a b → Wire s a b
  | Sum.inl (t,j) => if ht : t.val=0 then Sum.inr j else
      Sum.inl ⟨⟨2*t.val-1,row_index_lt t ht⟩,Fin.cast (row_bundle a b t ht).symm j⟩
  | Sum.inr (t,j) =>
      Sum.inl ⟨⟨2*t.val,col_index_lt t⟩,Fin.cast (col_bundle a b t).symm j⟩

def decodeWire {s a b : ℕ} : Wire s a b → CycleWire s a b
  | Sum.inl ⟨k,j⟩ => if hk : k.val%2=0 then
      Sum.inr (⟨k.val/2,by omega⟩,Fin.cast (by simp only [bundle,hk,ite_true]) j)
    else Sum.inl (⟨k.val/2+1,by omega⟩,Fin.cast (by simp only [bundle,hk,ite_false]) j)
  | Sum.inr j => Sum.inl (0,j)

lemma decode_encode {s a b : ℕ} (w : CycleWire s a b) : decodeWire (encodeWire w)=w := by
  rcases w with ⟨t,j⟩ | ⟨t,j⟩
  · by_cases ht : t.val=0
    · have he : t=0 := Fin.ext ht
      simp [encodeWire,decodeWire,he]
    · have ho := row_index_odd t ht
      simp only [encodeWire,dite_eq_right ht,decodeWire,dite_eq_right ho,Fin.cast_cast,Fin.cast_eq_self]
      congr 2
      apply Fin.ext
      dsimp only
      omega
  · simp only [encodeWire,decodeWire,Nat.mul_mod_right,dite_eq_left,Fin.cast_cast,Fin.cast_eq_self]
    congr 2
    apply Fin.ext
    dsimp only
    omega

lemma encode_decode {s a b : ℕ} (w : Wire s a b) : encodeWire (decodeWire w)=w := by
  rcases w with ⟨k,j⟩ | j
  · by_cases hk : k.val%2=0
    · simp only [decodeWire,dite_eq_left hk,encodeWire]
      congr 1
      apply Sigma.ext
      · apply Fin.ext
        dsimp only
        omega
      · exact (Fin.heq_ext_iff (by congr 1; apply Fin.ext; dsimp; omega)).mpr rfl
    · have hp : k.val/2+1≠0 := by omega
      simp only [decodeWire,dite_eq_right hk,encodeWire,Fin.val_mk,dite_eq_right hp]
      congr 1
      apply Sigma.ext
      · apply Fin.ext
        dsimp only
        omega
      · exact (Fin.heq_ext_iff (by congr 1; apply Fin.ext; dsimp; omega)).mpr rfl
  · rfl

def wireEquiv (s a b : ℕ) : CycleWire s a b ≃ Wire s a b where
  toFun := encodeWire
  invFun := decodeWire
  left_inv := decode_encode
  right_inv := encode_decode

end LogConcaveSampling.CycleTrace

end

end

section

noncomputable section
namespace LogConcaveSampling.CycleTrace
open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]

def weight (A : Matrix I J ℝ) {n : ℕ} (i k : I)
    (r : Fin n → I) (c : Fin (n+1) → J) : ℝ :=
  ∏ t : Fin (n+1), A (Fin.cons (α := fun _ => I) i r t) (c t) * A (Fin.snoc (α := fun _ => I) r k t) (c t)

omit [Fintype I] [Fintype J] [DecidableEq I] in
lemma weight_cons (A : Matrix I J ℝ) {n : ℕ} (i k l : I) (j : J)
    (r : Fin n → I) (c : Fin (n+1) → J) :
    weight A i k (Fin.cons l r) (Fin.cons j c) =
      (A i j * A l j) * weight A l k r c := by
  unfold weight
  rw [Fin.prod_univ_succ, ←Fin.cons_snoc_eq_snoc_cons]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem power_entry (A : Matrix I J ℝ) (n : ℕ) (i k : I) :
    ((A*A.transpose)^(n+1)) i k =
      ∑ r : Fin n → I, ∑ c : Fin (n+1) → J, weight A i k r c := by
  induction n generalizing i k with
  | zero =>
    conv_lhs => rw [Nat.zero_add, pow_one]
    rw [Matrix.mul_apply]
    conv_rhs => rw [Fintype.sum_unique]
    conv_rhs => rw [←(Fin.consEquiv (fun _ : Fin 1 => J)).sum_comp]
    simp only [Fintype.sum_prod_type, Fintype.sum_unique]
    apply Finset.sum_congr rfl
    intro j _
    have hs : Fin.snoc (α := fun _ => I) (default : Fin 0 → I) k 0 = k :=
      Fin.snoc_last _ _
    simp [weight, Matrix.transpose_apply, hs]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, ih, Finset.sum_mul,
      Finset.mul_sum]
    rw [←(Fin.consEquiv (fun _ : Fin (n+1) => I)).sum_comp]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro r _
    conv_rhs => rw [←(Fin.consEquiv (fun _ : Fin (n+2) => J)).sum_comp]
    simp only [Fintype.sum_prod_type]
    change (∑ c, ∑ j, A i j*A l j*weight A l k r c) =
      ∑ j, ∑ c, weight A i k (Fin.cons l r) (Fin.cons j c)
    simp_rw [weight_cons]
    rw [Finset.sum_comm]

theorem trace_power (A : Matrix I J ℝ) (n : ℕ) :
    ((A*A.transpose)^(n+1)).trace =
      ∑ i, ∑ r : Fin n → I, ∑ c : Fin (n+1) → J, weight A i i r c := by
  simp only [Matrix.trace, Matrix.diag, power_entry]

def advance {n : ℕ} (t : Fin (n+1)) : Fin (n+1) :=
  if h : t.val+1<n+1 then ⟨t.val+1,h⟩ else 0

omit [Fintype I] [Fintype J] [DecidableEq I] in
lemma snoc_eq_advance {n : ℕ} (i : I) (r : Fin n → I) (t : Fin (n+1)) :
    Fin.snoc (α := fun _ => I) r i t = Fin.cons (α := fun _ => I) i r (advance t) := by
  refine Fin.lastCases ?_ (fun k => ?_) t
  · simp [advance]
  · have hk : k.val+1<n+1 := by omega
    simp only [Fin.snoc_castSucc, advance, Fin.val_castSucc, dite_eq_left hk]
    change r k = Fin.cons (α := fun _ => I) i r k.succ
    simp only [Fin.cons_succ]

def closedWeight (A : Matrix I J ℝ) {n : ℕ}
    (r : Fin (n+1) → I) (c : Fin (n+1) → J) : ℝ :=
  ∏t,A (r t) (c t)*A (r (advance t)) (c t)

omit [Fintype I] [Fintype J] [DecidableEq I] in
lemma closedWeight_cons (A : Matrix I J ℝ) {n : ℕ}
    (i : I) (r : Fin n → I) (c : Fin (n+1) → J) :
    closedWeight A (Fin.cons i r) c = weight A i i r c := by
  simp only [closedWeight, weight, snoc_eq_advance]

theorem trace_power_colors (A : Matrix I J ℝ) (n : ℕ) :
    ((A*A.transpose)^(n+1)).trace =
      ∑r : Fin (n+1) → I,∑c : Fin (n+1) → J,closedWeight A r c := by
  rw [trace_power, ←(Fin.consEquiv (fun _ : Fin (n+1) => I)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk, closedWeight_cons]

end LogConcaveSampling.CycleTrace

end

end

section

noncomputable section
namespace LogConcaveSampling.CycleTrace
open AdjointRemoval
open scoped Classical BigOperators

variable {s a b : ℕ}

lemma right_row_lt (t : Fin (s+1)) (ht : t.val≠s) : 2*t.val+1<2*s+1 := by omega
lemma right_row_bundle (t : Fin (s+1)) (ht : t.val≠s) :
    bundle a b ⟨2*t.val+1,right_row_lt t ht⟩=a := by simp [bundle]

def encodeSlot (t : Fin (s+1)) (z : Fin 2) :
    Fin a ⊕ Fin b → ChainSlot (bundle a b) a (primaryPair s (t,z))
  | Sum.inl j => if hz : z.val=0 then
      if ht : t.val=0 then ⟨Sum.inr (Sum.inl j),by
        change 0=primaryPair s (t,z)
        apply Fin.ext
        simp only [Fin.val_zero,primaryPair_val]
        omega⟩
      else ⟨Sum.inl ⟨⟨2*t.val-1,row_index_lt t ht⟩,Fin.cast (row_bundle a b t ht).symm j⟩,by
        apply Or.inr
        apply Fin.ext
        simp only [Fin.val_succ,primaryPair_val]
        omega⟩
    else if ht : t.val=s then ⟨Sum.inr (Sum.inr j),by
        change Fin.last (2*s+1)=primaryPair s (t,z)
        apply Fin.ext
        simp only [Fin.val_last,primaryPair_val]
        omega⟩
      else ⟨Sum.inl ⟨⟨2*t.val+1,right_row_lt t ht⟩,Fin.cast (right_row_bundle t ht).symm j⟩,by
        apply Or.inl
        apply Fin.ext
        simp only [Fin.val_castSucc,primaryPair_val]
        omega⟩
  | Sum.inr j => ⟨Sum.inl ⟨⟨2*t.val,col_index_lt t⟩,Fin.cast (col_bundle a b t).symm j⟩,by
      change ((⟨2*t.val,col_index_lt t⟩ : Fin (2*s+1)).castSucc=primaryPair s (t,z)) ∨
        ((⟨2*t.val,col_index_lt t⟩ : Fin (2*s+1)).succ=primaryPair s (t,z))
      fin_cases z
      · exact Or.inl (Fin.ext (by simp))
      · exact Or.inr (Fin.ext (by simp))⟩

def decodeTraceSlot : TraceEdge (bundle (s:=s) a b) a → Fin a ⊕ Fin b
  | Sum.inl ⟨k,j⟩ => if hk : k.val%2=0 then
      Sum.inr (Fin.cast (by simp only [bundle,hk,ite_true]) j)
    else Sum.inl (Fin.cast (by simp only [bundle,hk,ite_false]) j)
  | Sum.inr (Sum.inl j) => Sum.inl j
  | Sum.inr (Sum.inr j) => Sum.inl j

lemma decode_encodeSlot (t : Fin (s+1)) (z : Fin 2) (j : Fin a ⊕ Fin b) :
    decodeTraceSlot (encodeSlot t z j).val=j := by
  rcases j with j | j
  · by_cases hz : z.val=0
    · by_cases ht : t.val=0
      · simp only [encodeSlot,dite_eq_left hz,dite_eq_left ht,decodeTraceSlot]
      · simp only [encodeSlot,dite_eq_left hz,dite_eq_right ht,decodeTraceSlot,
          dite_eq_right (row_index_odd t ht),Fin.cast_cast,Fin.cast_eq_self]
    · by_cases ht : t.val=s
      · simp only [encodeSlot,dite_eq_right hz,dite_eq_left ht,decodeTraceSlot]
      · have ho : (2*t.val+1)%2≠0 := by omega
        simp only [encodeSlot,dite_eq_right hz,dite_eq_right ht,decodeTraceSlot,
          dite_eq_right ho,Fin.cast_cast,Fin.cast_eq_self]
  · simp [encodeSlot,decodeTraceSlot]

lemma encode_decodeSlot (t : Fin (s+1)) (z : Fin 2)
    (u : ChainSlot (bundle a b) a (primaryPair s (t,z))) :
    encodeSlot t z (decodeTraceSlot u.val)=u := by
  apply Subtype.ext
  rcases u with ⟨⟨k,j⟩| (j|j),hu⟩
  · have hv : k.val=2*t.val+z.val ∨ k.val+1=2*t.val+z.val := by
      change k.castSucc=primaryPair s (t,z) ∨ k.succ=primaryPair s (t,z) at hu
      rcases hu with h|h
      · exact Or.inl (by simpa only [Fin.val_castSucc,primaryPair_val] using congrArg Fin.val h)
      · exact Or.inr (by simpa only [Fin.val_succ,primaryPair_val] using congrArg Fin.val h)
    by_cases hk : k.val%2=0
    · have he : 2*t.val=k.val := by omega
      simp only [decodeTraceSlot,dite_eq_left hk,encodeSlot]
      congr 1
      apply Sigma.ext (Fin.ext he)
      exact (Fin.heq_ext_iff (congrArg (bundle a b) (Fin.ext he))).mpr rfl
    · by_cases hz : z.val=0
      · have ht : t.val≠0 := by omega
        have he : 2*t.val-1=k.val := by omega
        simp only [decodeTraceSlot,dite_eq_right hk,encodeSlot,dite_eq_left hz,dite_eq_right ht]
        congr 1
        apply Sigma.ext (Fin.ext he)
        exact (Fin.heq_ext_iff (congrArg (bundle a b) (Fin.ext he))).mpr rfl
      · have ht : t.val≠s := by omega
        have he : 2*t.val+1=k.val := by omega
        simp only [decodeTraceSlot,dite_eq_right hk,encodeSlot,dite_eq_right hz,dite_eq_right ht]
        congr 1
        apply Sigma.ext (Fin.ext he)
        exact (Fin.heq_ext_iff (congrArg (bundle a b) (Fin.ext he))).mpr rfl
  · have hv : 0=2*t.val+z.val := by
      change 0=primaryPair s (t,z) at hu
      simpa only [Fin.val_zero,primaryPair_val] using congrArg Fin.val hu
    have hz : z.val=0 := by omega
    have ht : t.val=0 := by omega
    simp only [decodeTraceSlot,encodeSlot,dite_eq_left hz,dite_eq_left ht]
  · have hv : 2*s+1=2*t.val+z.val := by
      change Fin.last (2*s+1)=primaryPair s (t,z) at hu
      simpa only [Fin.val_last,primaryPair_val] using congrArg Fin.val hu
    have hz : z.val≠0 := by omega
    have ht : t.val=s := by omega
    simp only [decodeTraceSlot,encodeSlot,dite_eq_right hz,dite_eq_left ht]

def slotEquiv (t : Fin (s+1)) (z : Fin 2) :
    (Fin a ⊕ Fin b) ≃ ChainSlot (bundle a b) a (primaryPair s (t,z)) where
  toFun := encodeSlot t z
  invFun := fun u => decodeTraceSlot u.val
  left_inv := decode_encodeSlot t z
  right_inv := encode_decodeSlot t z

def slotEquivAt (i : Primary s) : (Fin a ⊕ Fin b) ≃ ChainSlot (bundle a b) a i where
  toFun u := ⟨(encodeSlot ((primaryPair s).symm i).1 ((primaryPair s).symm i).2 u).val,by
    have h := (encodeSlot ((primaryPair s).symm i).1 ((primaryPair s).symm i).2 u).property
    simpa only [Prod.eta,Equiv.apply_symm_apply] using h⟩
  invFun u := decodeTraceSlot u.val
  left_inv u := decode_encodeSlot _ _ u
  right_inv u := by
    apply Subtype.ext
    let v : ChainSlot (bundle a b) a
        (primaryPair s (((primaryPair s).symm i).1,((primaryPair s).symm i).2)) :=
      ⟨u.val,by simpa only [Prod.eta,Equiv.apply_symm_apply] using u.property⟩
    change (encodeSlot ((primaryPair s).symm i).1 ((primaryPair s).symm i).2
      (decodeTraceSlot u.val)).val=u.val
    exact congrArg (fun w : ChainSlot (bundle a b) a
      (primaryPair s (((primaryPair s).symm i).1,((primaryPair s).symm i).2)) => w.val)
      (encode_decodeSlot _ _ v)

@[simp] lemma slotEquivAt_pair (t : Fin (s+1)) (z : Fin 2) (u : Fin a ⊕ Fin b) :
    slotEquivAt (primaryPair s (t,z)) u=encodeSlot t z u := by
  apply Subtype.ext
  change (encodeSlot ((primaryPair s).symm (primaryPair s (t,z))).1
    ((primaryPair s).symm (primaryPair s (t,z))).2 u).val = _
  rw [Equiv.symm_apply_apply]

lemma close_encodeSlot_col (t : Fin (s+1)) (z : Fin 2) (j : Fin b) :
    closeTrace (bundle a b) a (encodeSlot t z (Sum.inr j)).val =
      encodeWire (Sum.inr (t,j)) := rfl

def rowAt (t : Fin (s+1)) (z : Fin 2) : Fin (s+1) :=
  if z.val=0 then t else advance t

lemma close_encodeSlot_row (t : Fin (s+1)) (z : Fin 2) (j : Fin a) :
    closeTrace (bundle a b) a (encodeSlot t z (Sum.inl j)).val =
      encodeWire (Sum.inl (rowAt t z,j)) := by
  by_cases hz : z.val=0
  · rw [show rowAt t z=t from ite_eq_left hz]
    by_cases ht : t.val=0
    · simp only [encodeSlot,dite_eq_left hz,dite_eq_left ht,closeTrace,encodeWire]
    · simp only [encodeSlot,dite_eq_left hz,dite_eq_right ht,closeTrace,encodeWire]
  · rw [show rowAt t z=advance t from ite_eq_right hz]
    by_cases ht : t.val=s
    · have ha : advance t=0 := by simp [advance,ht]
      rw [ha]
      change closeTrace (bundle a b) a (encodeSlot t z (Sum.inl j)).val=Sum.inr j
      simp only [encodeSlot,dite_eq_right hz,dite_eq_left ht,closeTrace]
    · have hp : t.val+1<s+1 := by omega
      have hn : (advance t).val≠0 := by
        simp only [advance,dite_eq_left hp]
        omega
      simp only [encodeSlot,dite_eq_right hz,dite_eq_right ht,closeTrace,encodeWire,dite_eq_right hn]
      congr 1
      apply Sigma.ext
      · apply Fin.ext
        simp only [advance,dite_eq_left hp]
        omega
      · exact (Fin.heq_ext_iff (by
          congr 1
          apply Fin.ext
          simp only [advance,dite_eq_left hp]
          omega)).mpr rfl

end LogConcaveSampling.CycleTrace

end

end

section

noncomputable section
namespace LogConcaveSampling.CycleTrace
open AdjointRemoval MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {s a b d : ℕ}

abbrev RowColors (s a d : ℕ) := Fin (s+1) → Fin a → Fin d

def colorEquiv (s a b d : ℕ) :
    TraceColors (bundle (s:=s) a b) a d ≃ (RowColors s a d × RowColors s b d) where
  toFun c := (fun t j => c (encodeWire (Sum.inl (t,j))),
    fun t j => c (encodeWire (Sum.inr (t,j))))
  invFun rc w := Sum.elim (fun x => rc.1 x.1 x.2) (fun x => rc.2 x.1 x.2) (decodeWire w)
  left_inv c := by
    funext w
    change Sum.elim (fun x => c (encodeWire (Sum.inl x)))
      (fun x => c (encodeWire (Sum.inr x))) (decodeWire w)=c w
    conv_rhs => rw [←encode_decode w]
    cases decodeWire w <;> rfl
  right_inv rc := by
    apply Prod.ext <;> funext t j <;>
      simp only [decode_encode,Sum.elim_inl,Sum.elim_inr]

def liftField (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    (i : Primary s) (c : ChainSlot (bundle a b) a i → Fin d) : Fin d → Point d → ℝ :=
  F (c ∘ slotEquivAt i)

lemma chainField_lift_pair (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    (c : TraceColors (bundle (s:=s) a b) a d) (t : Fin (s+1)) (z : Fin 2) :
    chainField (bundle a b) a (liftField F) c (primaryPair s (t,z)) =
      F (Sum.elim ((colorEquiv s a b d c).1 (rowAt t z))
        ((colorEquiv s a b d c).2 t)) := by
  unfold chainField liftField
  apply congrArg F
  funext j
  rcases j with j | j
  · simp only [Function.comp_apply,slotEquivAt_pair,close_encodeSlot_row,colorEquiv,
      Equiv.coe_fn_mk,Sum.elim_inl]
  · simp only [Function.comp_apply,slotEquivAt_pair,close_encodeSlot_col,colorEquiv,
      Equiv.coe_fn_mk,Sum.elim_inr]

def adjointMatrix (H : Point d → ℝ) (v : Fin d → Point d)
    (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ) (x : Point d) :
    Matrix (Fin a → Fin d) (Fin b → Fin d) ℝ :=
  fun r c => tensorAdjoint H v (F (Sum.elim r c)) x

lemma product_chain_lift (H : Point d → ℝ) (v : Fin d → Point d)
    (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    (c : TraceColors (bundle (s:=s) a b) a d) (x : Point d) :
    (∏i : Primary s,tensorAdjoint H v (chainField (bundle a b) a (liftField F) c i) x) =
      closedWeight (adjointMatrix H v F x)
        (colorEquiv s a b d c).1 (colorEquiv s a b d c).2 := by
  rw [←(primaryPair s).prod_comp]
  simp only [Fintype.prod_prod_type,chainField_lift_pair,Fin.prod_univ_two,
    rowAt,Fin.val_zero,Fin.val_one,ite_true,ite_false,one_ne_zero,
    closedWeight,adjointMatrix]

theorem trace_eq_chain (H : Point d → ℝ) (v : Fin d → Point d)
    (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ) (x : Point d) :
    ((adjointMatrix H v F x*(adjointMatrix H v F x).transpose)^(s+1)).trace =
      ∑c : TraceColors (bundle (s:=s) a b) a d,
        ∏i : Primary s,tensorAdjoint H v (chainField (bundle a b) a (liftField F) c i) x := by
  calc
    _ = ∑rc : RowColors s a d × RowColors s b d,
        closedWeight (adjointMatrix H v F x) rc.1 rc.2 := by
      rw [trace_power_colors,Fintype.sum_prod_type]
    _ = ∑c : TraceColors (bundle (s:=s) a b) a d,
        closedWeight (adjointMatrix H v F x)
          (colorEquiv s a b d c).1 (colorEquiv s a b d c).2 :=
      ((colorEquiv s a b d).sum_comp _).symm
    _ = _ := by simp only [product_chain_lift]

end LogConcaveSampling.CycleTrace

end

end

end

end OAI
