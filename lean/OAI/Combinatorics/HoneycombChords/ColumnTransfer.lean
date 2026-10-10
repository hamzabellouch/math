import OAI.Combinatorics.HoneycombChords.PlanarDiagrams

namespace OAI

/-!
# Column transfer and occupancy normalization

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped BigOperators

lemma act_prefix (t : TileWeights) (pre : List Spin) (i : ℕ) (f : DiluteState)
    (xs : List Spin) :
    act t (pre.length+i) f (pre++xs) = act t i (fun ys => f (pre++ys)) xs := by
  induction pre generalizing f with
  | nil => simp
  | cons a pre ih =>
    simpa [act,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (ih (fun ys => f (a::ys)))

lemma planarRow_prefix (pre : List Spin) (i : ℕ) (ts : List TileWeights)
    (f : DiluteState) (xs : List Spin) :
    planarRow (pre.length+i) ts f (pre++xs) =
      planarRow i ts (fun ys => f (pre++ys)) xs := by
  induction ts generalizing i f with
  | nil => rfl
  | cons t ts ih =>
    simp only [planarRow]
    rw [show pre.length+i+1=pre.length+(i+1) by omega,ih]
    congr 1
    funext ys
    exact act_prefix t pre i f ys

lemma sum_spin_vectors_succ {n : ℕ} (F : (Fin (n+1) → Spin) → ℂ) :
    (∑ τ, F τ) = ∑ a : Spin, ∑ τ : Fin n → Spin, F (Fin.cons (α:=fun _=>Spin) a τ) := by
  rw [←(Fin.consEquiv (fun _ : Fin (n+1) => Spin)).sum_comp F,Fintype.sum_prod_type]
  rfl

/-- Contract the vertical wires within a literal column and all right-side
input wires; the left-side output and upper auxiliary are not summed. -/
noncomputable def columnContraction (t : TileWeights) (n : ℕ) (f : DiluteState)
    (west : Fin n → Spin) (north : Spin) : ℂ :=
  ∑ east : Fin n → Spin, ∑ vertical : Fin n → Spin,
    (∏ j : Fin n, tile t (west j) ((Fin.snoc (α:=fun _=>Spin) vertical north) j.succ) (vertical j) (east j)) *
      f (((Fin.snoc (α:=fun _=>Spin) vertical north) 0) :: List.ofFn east)

lemma columnContraction_zero (t : TileWeights) (f : DiluteState)
    (west : Fin 0 → Spin) (north : Spin) :
    columnContraction t 0 f west north = f [north] := by
  simp [columnContraction,Fin.snoc_zero]

lemma columnContraction_succ (t : TileWeights) (n : ℕ) (f : DiluteState)
    (west : Fin (n+1) → Spin) (north : Spin) :
    columnContraction t (n+1) f west north =
      columnContraction t n (fun ys => act t 0 f (west 0 :: ys))
        (fun j => west j.succ) north := by
  unfold columnContraction
  rw [sum_spin_vectors_succ]
  simp_rw [sum_spin_vectors_succ,Fin.prod_univ_succ,
    ←Fin.cons_snoc_eq_snoc_cons,Fin.cons_succ,Fin.cons_zero,List.ofFn_succ]
  simp only [act,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro east heast
  conv_lhs =>
    arg 2
    ext firstEast
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro vertical hvertical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro south hsouth
  apply Finset.sum_congr rfl
  intro firstEast hfirstEast
  simp only [Fin.cons_zero,Fin.cons_succ]
  ring

/-- This is the exact tensor contraction equality for an arbitrary column,
including each internal spin once. No cancellation or eigenvalue input. -/
theorem planarRow_eq_columnContraction (t : TileWeights) (n : ℕ) (f : DiluteState)
    (west : Fin n → Spin) (north : Spin) :
    planarRow 0 (List.replicate n t) f (List.ofFn west ++ [north]) =
      columnContraction t n f west north := by
  induction n generalizing f with
  | zero => simp [planarRow,columnContraction_zero]
  | succ n ih =>
    rw [List.replicate_succ,List.ofFn_succ,List.cons_append,planarRow]
    rw [show 0+1=([west 0] : List Spin).length+0 by rfl]
    change planarRow (([west 0] : List Spin).length+0) (List.replicate n t)
      (act t 0 f) ([west 0] ++ (List.ofFn (fun j => west j.succ) ++ [north])) = _
    rw [planarRow_prefix,ih,columnContraction_succ]
    rfl

noncomputable def columnKernelSpin (t : TileWeights) (n : ℕ) (south north : Spin)
    (west east : Fin n → Spin) : ℂ :=
  ∑ vertical : Fin n → Spin,
    if (Fin.snoc (α:=fun _=>Spin) vertical north) 0=south then
      ∏ j : Fin n, tile t (west j) ((Fin.snoc (α:=fun _=>Spin) vertical north) j.succ)
        (vertical j) (east j) else 0

lemma columnContraction_delta (t : TileWeights) (n : ℕ) (south north : Spin)
    (west east : Fin n → Spin) :
    columnContraction t n (fun xs => if xs=south::List.ofFn east then 1 else 0) west north =
      columnKernelSpin t n south north west east := by
  classical
  unfold columnContraction columnKernelSpin
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro vertical hv
  simp only [List.cons.injEq,List.ofFn_injective.eq_iff,mul_ite,mul_one,mul_zero]
  by_cases hs : (Fin.snoc (α:=fun _=>Spin) vertical north) 0=south
  · simp [hs]
  · simp [hs]

theorem planarRow_delta (t : TileWeights) (n : ℕ) (south north : Spin)
    (west east : Fin n → Spin) :
    planarRow 0 (List.replicate n t) (fun xs => if xs=south::List.ofFn east then 1 else 0)
      (List.ofFn west++[north]) = columnKernelSpin t n south north west east := by
  rw [planarRow_eq_columnContraction,columnContraction_delta]

end CriticalHoneycomb.Transfer.PlanarNormalization


namespace CriticalHoneycomb.Transfer.RasterGrid
open scoped BigOperators

def spinEquiv : PlanarNormalization.Spin ≃ Fin 3 where
  toFun := PlanarNormalization.spinIndex
  invFun i := if i=1 then none else some (decide (i=2))
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[simp] lemma spinEquiv_apply (i : PlanarNormalization.Spin) : spinEquiv i = PlanarNormalization.spinIndex i := rfl

noncomputable def physicalWeights : PlanarNormalization.TileWeights :=
  ⟨(kappa:ℂ),(kappa^2:ℂ),(kappa^2:ℂ),(kappa^2:ℂ),0⟩

lemma sourceR_eq (t : PlanarNormalization.TileWeights) (p q : Fin 3 × Fin 3) :
    PlanarNormalization.sourceR t p q = Planar.sourceR t.a t.h t.v t.c t.d p q := rfl

lemma tile_physical (i j k l : PlanarNormalization.Spin) :
    PlanarNormalization.tile physicalWeights i j k l =
      Planar.sourceR (kappa:ℂ) (kappa^2:ℂ) (kappa^2:ℂ) (kappa^2:ℂ) 0
        (spinEquiv j,spinEquiv i) (spinEquiv k,spinEquiv l) := by
  rw [PlanarNormalization.tile_eq_sourceR,sourceR_eq]
  rfl

/-- Changing from vacant/arrow spins to the manuscript's +,0,- ordering. -/
def columnSpinEquiv (H : ℕ) : (Fin H → PlanarNormalization.Spin) ≃ Column H :=
  Equiv.piCongrRight (fun _ => spinEquiv)

@[simp] lemma columnSpinEquiv_apply {H : ℕ} (a : Fin H → PlanarNormalization.Spin) (i : Fin H) :
    columnSpinEquiv H a i = spinEquiv (a i) := rfl

lemma columnKernel_eq_spin (H : ℕ) (south north : PlanarNormalization.Spin)
    (west east : Fin H → PlanarNormalization.Spin) :
    columnKernel H (spinEquiv south) (spinEquiv north)
      (columnSpinEquiv H west) (columnSpinEquiv H east) =
      PlanarNormalization.columnKernelSpin physicalWeights H south north west east := by
  classical
  unfold columnKernel PlanarNormalization.columnKernelSpin
  rw [←(columnSpinEquiv H).sum_comp]
  apply Finset.sum_congr rfl
  intro vertical hv
  have hs : ∀ j : Fin (H+1),
      Fin.snoc (α:=fun _=> Fin 3) (columnSpinEquiv H vertical) (spinEquiv north) j =
      spinEquiv (Fin.snoc (α:=fun _=> PlanarNormalization.Spin) vertical north j) := by
    intro j
    cases j using Fin.lastCases <;> simp
  simp only [hs,Equiv.apply_eq_iff_eq]
  split_ifs with h
  · unfold columnProduct
    apply Finset.prod_congr rfl
    intro j hj
    rw [hs]
    exact (tile_physical _ _ _ _).symm
  · rfl

/-- Exact physical lattice-column transfer as the already normalized
planar cup/cap circuit. The boundary delta has not been replaced by any
probability or connectivity assumption. -/
theorem columnKernel_eq_planarRow (H : ℕ) (south north : PlanarNormalization.Spin)
    (west east : Fin H → PlanarNormalization.Spin) :
    columnKernel H (spinEquiv south) (spinEquiv north)
      (columnSpinEquiv H west) (columnSpinEquiv H east) =
      PlanarNormalization.planarRow 0 (List.replicate H physicalWeights)
        (fun xs => if xs=south::List.ofFn east then 1 else 0)
        (List.ofFn west++[north]) := by
  rw [columnKernel_eq_spin,PlanarNormalization.planarRow_delta]

end CriticalHoneycomb.Transfer.RasterGrid

namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped BigOperators

/-- Fix all occupied edges of a frontier, without fixing their orientations. -/
noncomputable def mask (o : List Bool) (f : DiluteState) : DiluteState :=
  fun xs => if occupancy xs = o then f xs else 0

lemma mask_embed (o p : List Bool) (f : State) :
    mask o (embed p f) = if o=p then embed p f else fun _ => 0 := by
  classical
  funext xs
  by_cases h : o=p
  · subst p
    by_cases hx : occupancy xs = o <;> simp [mask,embed,hx]
  · simp only [ite_eq_right h,mask,embed]
    split_ifs with hx hy
    · exact (h (hx.symm.trans hy)).elim
    · rfl
    · rfl

lemma mask_add (o : List Bool) (f g : DiluteState) :
    mask o (fun xs => f xs + g xs) = fun xs => mask o f xs + mask o g xs := by
  funext xs
  simp only [mask]
  split_ifs <;> simp

lemma mask_smul (o : List Bool) (z : ℂ) (f : DiluteState) :
    mask o (fun xs => z*f xs) = fun xs => z*mask o f xs := by
  funext xs
  simp only [mask]
  split_ifs <;> simp

lemma mask_zero (o : List Bool) : mask o (fun _ => 0) = fun _ => 0 := by
  funext xs
  simp [mask]

lemma mask_span (o : List Bool) {n : ℕ} {f : DiluteState}
    (hf : PlanarSpan n f) : PlanarSpan n (mask o f) := by
  induction hf with
  | zero => rw [mask_zero]; exact .zero
  | basis p k w hl hc =>
    rw [mask_embed]
    split_ifs
    · exact .basis p k w hl hc
    · exact .zero
  | add hf hg ihf ihg => rw [mask_add]; exact .add ihf ihg
  | smul z hf ihf => rw [mask_smul]; exact .smul z ihf

lemma mask_vacuum (o : List Bool) (n : ℕ) (f : DiluteState) :
    mask o f (List.replicate n none) =
      (if o=List.replicate n false then 1 else 0) * f (List.replicate n none) := by
  simp only [mask,occupancy,List.map_replicate,Option.isSome_none]
  split_ifs with ho ho ho <;> simp_all

/-- A fully resolved occupancy history. Summation now remains only over
orientations; it is not a sum over different unoriented configurations. -/
structure MaskedGate where
  weights : TileWeights
  site : ℕ
  output : List Bool

noncomputable def maskedAct (g : MaskedGate) (f : DiluteState) : DiluteState :=
  mask g.output (act g.weights g.site f)

lemma maskedAct_span {n : ℕ} (g : MaskedGate) (hi : g.site+1<n)
    {f : DiluteState} (hf : PlanarSpan n f) : PlanarSpan n (maskedAct g f) :=
  mask_span _ (act_span _ hi hf)

lemma maskedAct_vacuum {n : ℕ} (g : MaskedGate) (hi : g.site+1<n)
    {f : DiluteState} (hf : PlanarSpan n f) :
    maskedAct g f (List.replicate n none) =
      (if g.output=List.replicate n false then 1 else 0)*f (List.replicate n none) := by
  rw [maskedAct,mask_vacuum,act_vacuum _ hi hf]

lemma masked_history_vacuum {n : ℕ} (gs : List MaskedGate)
    (hg : ∀ g ∈ gs, g.site+1<n) {f : DiluteState} (hf : PlanarSpan n f) :
    (gs.foldl (fun f g => maskedAct g f) f) (List.replicate n none) =
      (gs.map (fun g => if g.output=List.replicate n false then (1:ℂ) else 0)).prod *
        f (List.replicate n none) := by
  induction gs generalizing f with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons,ih (by aesop) (maskedAct_span _ (hg g (by simp)) hf),
      maskedAct_vacuum _ (hg g (by simp)) hf]
    simp only [List.map_cons,List.prod_cons]
    ring

/-- Exact cancellation of each nonempty closed unoriented configuration,
not only cancellation after all configurations have been summed. -/
theorem nonempty_closed_history_zero {n : ℕ} (gs : List MaskedGate)
    (hg : ∀ g ∈ gs, g.site+1<n)
    (hne : ∃ g ∈ gs, g.output ≠ List.replicate n false) :
    (gs.foldl (fun f g => maskedAct g f)
      (embed (List.replicate n false) (fun _ => 1))) (List.replicate n none) = 0 := by
  have hf : PlanarSpan n (embed (List.replicate n false) (fun _ => 1)) :=
    PlanarSpan.basis (List.replicate n false) 0 .start (by simp) (by simp [List.count_replicate])
  rw [masked_history_vacuum gs hg hf]
  obtain ⟨g,hg,hne⟩ := hne
  have hz : (0:ℂ) ∈ gs.map (fun g => if g.output=List.replicate n false then (1:ℂ) else 0) := by
    exact List.mem_map.mpr ⟨g,hg,ite_eq_right hne⟩
  rw [List.prod_eq_zero_iff.mpr hz,zero_mul]

end CriticalHoneycomb.Transfer.PlanarNormalization

namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped BigOperators

/-- Physical tile with the positive center-count factor removed. The
forbidden double-return connectivity still has coefficient exactly zero. -/
noncomputable def resolvedWeights : TileWeights := ⟨1,1,1,1,0⟩

/-- After fixing all occupied wire sets, a physical honeycomb history is a
single planar word or zero, not a linear superposition of connectivities. -/
inductive Resolved (b n : ℕ) (root : State) : DiluteState → Prop
  | zero : Resolved b n root (fun _ => 0)
  | basis (o : List Bool) (k : ℕ) (w : PlanarWord b k)
      (hl : o.length=n) (hc : o.count true=b+2*k) :
      Resolved b n root (embed o (w.eval root))

lemma mask_disjoint_pair (out o p : List Bool) (f g : State) (hop : o≠p) :
    mask out (fun xs => embed o f xs + embed p g xs) = (fun _ => 0) ∨
    mask out (fun xs => embed o f xs + embed p g xs) = embed o f ∨
    mask out (fun xs => embed o f xs + embed p g xs) = embed p g := by
  rw [mask_add,mask_embed,mask_embed]
  by_cases ho : out=o
  · subst out
    simp [hop]
  · by_cases hp : out=p
    · subst out
      simp [ho]
    · simp [hp,ho]

lemma resolved_mask_pair {b n : ℕ} {root : State}
    (out o p : List Bool) (f g : State) (hop : o≠p)
    (hf : Resolved b n root (embed o f)) (hg : Resolved b n root (embed p g)) :
    Resolved b n root (mask out (fun xs => embed o f xs + embed p g xs)) := by
  rcases mask_disjoint_pair out o p f g hop with h|h|h <;> rw [h]
  · exact .zero
  · exact hf
  · exact hg

/-- Exact source physical local action at fixed input and output occupancy.
The positive κ-factors can be restored after this orientation calculation. -/
lemma resolved_step {b n i : ℕ} (hb : b≤1) (hi : i+1<n) (out : List Bool)
    {root : State} {f : DiluteState} (hf : Resolved b n root f) :
    Resolved b n root (mask out (act resolvedWeights i f)) := by
  cases hf with
  | zero => rw [act_zero,mask_zero]; exact .zero
  | basis o k w hl hc =>
    obtain ⟨pre,a,b',post,rfl,hpre⟩ := two_at o i (by omega)
    subst i
    cases a <;> cases b'
    · rw [act_empty_at]
      simp only [resolvedWeights,one_mul]
      apply resolved_mask_pair
      · simp
      · exact .basis _ k w hl hc
      · have hip : pre.count true ≤ b+2*k := by simp [List.count_append] at hc; omega
        exact .basis _ (k+1) (.insert w (pre.count true) hip)
          (by simpa using hl) (by simp_all [List.count_append]; omega)
    · rw [act_right_at]
      simp only [resolvedWeights,one_mul]
      apply resolved_mask_pair
      · simp
      · exact .basis _ k w hl hc
      · exact .basis _ k w (by simpa using hl)
          (by simpa [List.count_append,List.count_cons] using hc)
    · rw [act_left_at]
      simp only [resolvedWeights,one_mul]
      apply resolved_mask_pair
      · simp
      · exact .basis _ k w hl hc
      · exact .basis _ k w (by simpa using hl)
          (by simpa [List.count_append,List.count_cons] using hc)
    · have hk : 0<k := by simp [List.count_append] at hc; omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
      have hip : pre.count true ≤ b+2*k := by simp [List.count_append] at hc ⊢; omega
      rw [act_full_at]
      simp only [resolvedWeights,one_mul,zero_mul,add_zero]
      apply resolved_mask_pair
      · simp
      · exact .basis _ (k+1) w hl hc
      · exact .basis _ k (.erase w (pre.count true) hip) (by simpa using hl)
          (by simp [List.count_append] at hc ⊢; omega)

structure ResolvedGate where
  site : ℕ
  output : List Bool

noncomputable def resolvedAct (g : ResolvedGate) (f : DiluteState) : DiluteState :=
  mask g.output (act resolvedWeights g.site f)

lemma resolved_history {b n : ℕ} (hb : b≤1) (gs : List ResolvedGate)
    (hg : ∀ g∈gs, g.site+1<n) {root : State} {f : DiluteState}
    (hf : Resolved b n root f) :
    Resolved b n root (gs.foldl (fun f g => resolvedAct g f) f) := by
  induction gs generalizing f with
  | nil => exact hf
  | cons g gs ih =>
    exact ih (by aesop) (resolved_step hb (hg g (by simp)) _ hf)


/-- Put the same orientation on the occupied positions of a frontier. This
is used only for frontiers with exactly one occupied edge. -/
def arrowState (o : List Bool) (a : Bool) : List Spin :=
  o.map (fun b => if b then some a else none)

lemma occupancy_arrowState (o : List Bool) (a : Bool) :
    occupancy (arrowState o a)=o := by
  induction o with
  | nil => rfl
  | cons b o ih => cases b <;> simp [arrowState,occupancy] at * <;> exact ih

lemma orientations_arrowState (o : List Bool) (a : Bool) :
    orientations (arrowState o a)=List.replicate (o.count true) a := by
  induction o with
  | nil => rfl
  | cons b o ih =>
    cases b <;> simp [arrowState,orientations,List.replicate_succ] at * <;> exact ih

lemma embed_arrowState (o p : List Bool) (f : State) (a : Bool) :
    embed o f (arrowState p a) = if p=o then f (List.replicate (p.count true) a) else 0 := by
  simp [embed,occupancy_arrowState,orientations_arrowState]

/-- The exact phase normalization with every unoriented history fixed.
There is no positivity assumption on the complex local phases. -/
theorem resolved_one_strand {n : ℕ} {root : State} {f : DiluteState}
    (hf : Resolved 1 n root f) (out : List Bool) (hout : out.count true=1) :
    (∀ a : Bool, f (arrowState out a)=0) ∨
    (∀ a : Bool, f (arrowState out a)=root [a]) := by
  cases hf with
  | zero => exact Or.inl (fun _ => rfl)
  | basis o k w hl hc =>
    by_cases ho : out=o
    · subst o
      have hk : k=0 := by omega
      subst k
      rcases one_strand_zero_or_identity w root with h|h
      · exact Or.inl (fun a => by simpa [embed_arrowState,hout] using h a)
      · exact Or.inr (fun a => by simpa [embed_arrowState,hout] using h a)
    · exact Or.inl (fun a => by simp [embed_arrowState,ho])

theorem resolved_history_one_strand {n : ℕ} (gs : List ResolvedGate)
    (hg : ∀ g∈gs, g.site+1<n) (input out : List Bool)
    (hi : input.length=n) (hinput : input.count true=1) (hout : out.count true=1)
    (root : State) :
    (∀ a : Bool, (gs.foldl (fun f g => resolvedAct g f) (embed input root))
      (arrowState out a)=0) ∨
    (∀ a : Bool, (gs.foldl (fun f g => resolvedAct g f) (embed input root))
      (arrowState out a)=root [a]) := by
  have hf : Resolved 1 n root (embed input root) :=
    .basis input 0 .start hi (by simpa using hinput)
  exact resolved_one_strand (resolved_history (by omega : 1≤1) gs hg hf) out hout

end CriticalHoneycomb.Transfer.PlanarNormalization

end OAI
