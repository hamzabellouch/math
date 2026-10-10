import OAI.Algebra.Drinfeld.Hexagon

namespace OAI

noncomputable section

namespace RealDeligneDrinfeld.KZHomogeneous
open DeligneDrinfeld DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.CutoffPrimitiveExtract DeligneDrinfeld.TruncatedWords
abbrev V (N : ℕ) : A ℝ Bool := normalVal N (KZComparison.value N)
def q (n : ℕ) : L := if h:0<n then (KZ_value_lie n n h le_rfl).choose else 0
 theorem q_homogeneous (n : ℕ) : q n∈Ln n := by
  unfold q
  split_ifs with h
  · rw [Ln,WeightBridge.piece_eq]
    exact (KZ_value_lie n n h le_rfl).choose_spec.1
  · exact Submodule.zero_mem _
 theorem q_embed (n : ℕ) (hn : 0<n) : embed (q n)=TensorProjection.piece n (V n) := by
  simp only [q,dite_eq_left hn]
  exact (KZ_value_lie n n hn le_rfl).choose_spec.2
 theorem normal_mem {N k : ℕ} {u : CutoffDepth.Q ℝ N} (hu : u∈filtration ∅ N k) :
    normalVal N u∈above (fun _ => 1) k := by
  obtain ⟨p,hp,rfl⟩ := hu
  change normalVal N (quotient ∅ N p)∈_
  rw [normalVal_quotient]
  exact project_preserves hp
 theorem normal_below (N : ℕ) (u : CutoffDepth.Q ℝ N) : normalVal N u∈below (fun _ => 1) N :=
  (TruncatedFree.normal N u).property
 theorem quotient_normal (N : ℕ) (u : CutoffDepth.Q ℝ N) : quotient ∅ N (normalVal N u)=u := by
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (relations (∅:Set (A ℝ Bool)) N) u
  change quotient ∅ N (normalVal N (quotient ∅ N p))=quotient ∅ N p
  rw [normalVal_quotient]
  have hh := quotient_above (∅:Set (A ℝ Bool)) N (TruncatedFree.sub_trunc_above N p)
  rw [map_sub] at hh
  exact (sub_eq_zero.mp hh).symm
 theorem value_above (N : ℕ) : V N∈above (fun _ => 1) 1 := by
  apply normal_mem
  rw [←KZRealLog.value]
  exact KZRealLog.raises N false true 0 1 (filtration_one ∅ N)
 theorem q_embed_zero : embed (q 0)=TensorProjection.piece 0 (V 0) := by
  change (0:A ℝ Bool)=TensorProjection.piece 0 (V 0)
  symm
  exact project_eq_zero (value_above 0) (by intro w hw hh; change 1≤degree (fun _ => 1) w at hw; omega)
 theorem piece_drop (M N n : ℕ) (hNM : N≤M) (hn : n≤N) (u : CutoffDepth.Q ℝ M) :
    TensorProjection.piece n (normalVal M u)=
      TensorProjection.piece n (normalVal N (CutoffDiagonal.drop M N hNM u)) := by
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (relations (∅:Set (A ℝ Bool)) M) u
  change TensorProjection.piece n (normalVal M (quotient ∅ M p))=
    TensorProjection.piece n (normalVal N (CutoffDiagonal.drop M N hNM (quotient ∅ M p)))
  rw [drop_quotient,normalVal_quotient,normalVal_quotient,piece_trunc _ _ (hn.trans hNM),piece_trunc _ _ hn]
 theorem q_embed_any (N n : ℕ) (hn : n≤N) : embed (q n)=TensorProjection.piece n (V N) := by
  have hh := piece_drop N n n hn le_rfl (KZComparison.value N)
  rw [KZCutoffComparison.value_drop] at hh
  rw [hh]
  by_cases h : 0<n
  · exact q_embed n h
  · have he : n=0 := by omega
    subst n
    exact q_embed_zero
 theorem residual_above (N n : ℕ) (hn : n≤N+1) :
    V N-∑ i∈Finset.range n,embed (q i)∈above (fun _ => 1) n := by
  induction n with
  | zero => simpa only [Finset.range_zero,Finset.sum_empty,sub_zero] using TruncatedFree.all_ge_zero (V N)
  | succ n ih =>
    have hh := subtract_piece_above (ih (by omega))
    have he : TensorProjection.piece n (V N-∑ i∈Finset.range n,embed (q i))=embed (q n) := by
      rw [map_sub,map_sum,←q_embed_any N n (by omega)]
      have hz : ∑ i∈Finset.range n,TensorProjection.piece n (embed (q i))=0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [piece_homogeneous (WeightBridge.embed_homogeneous (q_homogeneous i)),ite_eq_right (by have hi' := Finset.mem_range.mp hi; omega)]
      rw [hz,sub_zero]
    rw [he] at hh
    rw [Finset.sum_range_succ]
    simpa only [sub_add_eq_sub_sub] using hh

end RealDeligneDrinfeld.KZHomogeneous

namespace DeligneDrinfeld
namespace CategoryGauge
variable {R M N O P : Type*} [CommRing R] [LieRing M] [LieAlgebra R M]
    [LieRing N] [LieAlgebra R N]

structure Data (R M O : Type*) [CommRing R] [LieRing M] [LieAlgebra R M] where
  d : LieDerivation R M M
  h : O → M

def unit (g : Data R M O) (p q : O) : M := g.h q-g.h p

def loop (g : Data R M O) (p : O) : LieDerivation R M M :=
  g.d-LieDerivation.inner R M M (g.h p)

@[simp] theorem loop_apply (g : Data R M O) (p : O) (x : M) :
    loop g p x=g.d x+⁅g.h p,x⁆ := by
  change g.d x-⁅x,g.h p⁆=g.d x+⁅g.h p,x⁆
  rw [←lie_skew (g.h p) x]
  abel

theorem unit_cocycle (g : Data R M O) (p q r : O) : unit g p r=unit g p q+unit g q r := by
  unfold unit
  abel

theorem loop_change (g : Data R M O) (p q : O) (x : M) :
    loop g q x=loop g p x+⁅unit g p q,x⁆ := by
  simp only [loop_apply,unit,sub_lie]
  abel

def commutator (g k : Data R M O) : Data R M O where
  d := ⁅g.d,k.d⁆
  h p := g.d (k.h p)-k.d (g.h p)+⁅g.h p,k.h p⁆

theorem loop_commutator (g k : Data R M O) (p : O) :
    loop (commutator g k) p=⁅loop g p,loop k p⁆ := by
  ext x
  simp only [loop_apply,commutator,LieDerivation.lie_apply,map_add,
    LieDerivation.apply_lie_eq_add,add_lie,sub_lie,lie_add]
  rw [lie_lie (g.h p) (k.h p) x]
  rw [lie_lie (k.h p) (g.h p) x]
  abel

theorem unit_commutator (g k : Data R M O) (p q : O) :
    unit (commutator g k) p q=
      loop g p (unit k p q)-loop k p (unit g p q)+⁅unit g p q,unit k p q⁆ := by
  simp only [unit,commutator,loop_apply,map_sub,lie_sub,sub_lie]
  rw [←lie_skew (k.h p) (g.h p),←lie_skew (k.h p) (g.h q)]
  abel

def Compatible (F : M →ₗ⁅R⁆ N) (f : O → P) (g : Data R M O) (k : Data R N P) : Prop :=
  (∀ p q,unit k (f p) (f q)=F (unit g p q)) ∧
  (∀ p x,loop k (f p) (F x)=F (loop g p x))

theorem compatible_commutator (F : M →ₗ⁅R⁆ N) (f : O → P)
    {g₁ g₂ : Data R M O} {k₁ k₂ : Data R N P}
    (h₁ : Compatible F f g₁ k₁) (h₂ : Compatible F f g₂ k₂) :
    Compatible F f (commutator g₁ g₂) (commutator k₁ k₂) := by
  constructor
  · intro p q
    rw [unit_commutator,unit_commutator,h₁.1,h₂.1,h₁.2,h₂.2,map_add,map_sub,LieHom.map_lie]
  · intro p x
    rw [loop_commutator,loop_commutator,LieDerivation.lie_apply,LieDerivation.lie_apply,
      h₁.2,h₂.2,h₁.2,h₂.2,map_sub]

def zero : Data R M O := ⟨0,fun _ => 0⟩
def add (g k : Data R M O) : Data R M O := ⟨g.d+k.d,fun p => g.h p+k.h p⟩
def smul (c : R) (g : Data R M O) : Data R M O := ⟨c • g.d,fun p => c • g.h p⟩

@[simp] theorem zero_unit (p q : O) : unit (zero (R:=R) (M:=M)) p q=0 := by simp [unit,zero]
@[simp] theorem zero_loop (p : O) (x : M) : loop (zero (R:=R)) p x=0 := by simp [loop_apply,zero]
@[simp] theorem add_unit (g k : Data R M O) (p q : O) :
    unit (add g k) p q=unit g p q+unit k p q := by simp only [unit,add]; abel
@[simp] theorem add_loop (g k : Data R M O) (p : O) (x : M) :
    loop (add g k) p x=loop g p x+loop k p x := by simp only [loop_apply,add,LieDerivation.add_apply,add_lie]; abel
@[simp] theorem smul_unit (c : R) (g : Data R M O) (p q : O) :
    unit (smul c g) p q=c • unit g p q := by simp [unit,smul,smul_sub]
@[simp] theorem smul_loop (c : R) (g : Data R M O) (p : O) (x : M) :
    loop (smul c g) p x=c • loop g p x := by simp [loop_apply,smul,smul_add]

theorem compatible_zero (F : M →ₗ⁅R⁆ N) (f : O → P) : Compatible F f zero zero := by
  constructor <;> intros <;> simp [zero,unit,loop_apply]

theorem compatible_add (F : M →ₗ⁅R⁆ N) (f : O → P)
    {g₁ g₂ : Data R M O} {k₁ k₂ : Data R N P}
    (h₁ : Compatible F f g₁ k₁) (h₂ : Compatible F f g₂ k₂) :
    Compatible F f (add g₁ g₂) (add k₁ k₂) := by
  constructor
  · intro p q; simp only [add_unit,h₁.1,h₂.1,map_add]
  · intro p x; simp only [add_loop,h₁.2,h₂.2,map_add]

theorem compatible_smul (F : M →ₗ⁅R⁆ N) (f : O → P)
    {g : Data R M O} {k : Data R N P} (h : Compatible F f g k) (c : R) :
    Compatible F f (smul c g) (smul c k) := by
  constructor
  · intro p q; simp only [smul_unit,h.1,map_smul]
  · intro p x; simp only [smul_loop,h.2,map_smul]

theorem commutator_zero_unit {g k : Data R M O} {p q : O}
    (hg : unit g p q=0) (hk : unit k p q=0) : unit (commutator g k) p q=0 := by
  rw [unit_commutator,hg,hk,map_zero,map_zero,sub_zero,lie_zero,add_zero]

theorem commutator_zero_loop {g k : Data R M O} {p : O}
    (hg : loop g p=0) (hk : loop k p=0) : loop (commutator g k) p=0 := by
  rw [loop_commutator,hg,hk,lie_zero]

end CategoryGauge
end DeligneDrinfeld

namespace DeligneDrinfeld.CategoryGauge
variable {R M N O P : Type*} [CommRing R] [LieRing M] [LieAlgebra R M]
  [LieRing N] [LieAlgebra R N]

def EdgeCompatible (F : M →ₗ⁅R⁆ N) (p q : O) (s t : P)
    (g : Data R M O) (k : Data R N P) : Prop :=
  unit k s t=F (unit g p q) ∧ ∀ x,loop k s (F x)=F (loop g p x)

theorem edge_target (F : M →ₗ⁅R⁆ N) {p q : O} {s t : P}
    {g : Data R M O} {k : Data R N P} (h : EdgeCompatible F p q s t g k) (x : M) :
    loop k t (F x)=F (loop g q x) := by
  rw [loop_change k s t,loop_change g p q,h.1,h.2,map_add,LieHom.map_lie]

theorem edge_commutator (F : M →ₗ⁅R⁆ N) {p q : O} {s t : P}
    {g₁ g₂ : Data R M O} {k₁ k₂ : Data R N P}
    (h₁ : EdgeCompatible F p q s t g₁ k₁) (h₂ : EdgeCompatible F p q s t g₂ k₂) :
    EdgeCompatible F p q s t (commutator g₁ g₂) (commutator k₁ k₂) := by
  constructor
  · rw [unit_commutator,unit_commutator,h₁.1,h₂.1,h₁.2,h₂.2,map_add,map_sub,LieHom.map_lie]
  · intro x
    rw [loop_commutator,loop_commutator,LieDerivation.lie_apply,LieDerivation.lie_apply,
      h₁.2,h₂.2,h₁.2,h₂.2,map_sub]

theorem edge_zero (F : M →ₗ⁅R⁆ N) (p q : O) (s t : P) :
    EdgeCompatible F p q s t zero zero := by
  constructor <;> intros <;> simp [zero,unit,loop_apply]

theorem edge_add (F : M →ₗ⁅R⁆ N) {p q : O} {s t : P}
    {g₁ g₂ : Data R M O} {k₁ k₂ : Data R N P}
    (h₁ : EdgeCompatible F p q s t g₁ k₁) (h₂ : EdgeCompatible F p q s t g₂ k₂) :
    EdgeCompatible F p q s t (add g₁ g₂) (add k₁ k₂) := by
  constructor
  · rw [add_unit,add_unit,h₁.1,h₂.1,map_add]
  · intro x; rw [add_loop,add_loop,h₁.2,h₂.2,map_add]

theorem edge_smul (F : M →ₗ⁅R⁆ N) {p q : O} {s t : P}
    {g : Data R M O} {k : Data R N P} (h : EdgeCompatible F p q s t g k) (c : R) :
    EdgeCompatible F p q s t (smul c g) (smul c k) := by
  constructor
  · rw [smul_unit,smul_unit,h.1,map_smul]
  · intro x; rw [smul_loop,smul_loop,h.2,map_smul]

theorem commutator_kills {g k : Data R M O} {p : O} {x : M}
    (hg : loop g p x=0) (hk : loop k p x=0) : loop (commutator g k) p x=0 := by
  rw [loop_commutator,LieDerivation.lie_apply,hg,hk,map_zero,map_zero,sub_zero]

end DeligneDrinfeld.CategoryGauge

namespace RealDeligneDrinfeld.CategoricalValues
open DeligneDrinfeld.CategoryGauge

def swapObjects : Fin 3 → Fin 3 := ![1,0,2]
def rotateObjects : Fin 3 → Fin 3 := ![1,2,0]
def swapLie : L →ₗ⁅ℝ⁆ L := eval y x
def rotateLie : L →ₗ⁅ℝ⁆ L := eval y (-x-y)

structure Witness where
  three : DeligneDrinfeld.CategoryGauge.Data ℝ L (Fin 3)
  four : DeligneDrinfeld.CategoryGauge.Data ℝ T4 (Fin 5)
  swap : Compatible swapLie swapObjects three three
  rotate : Compatible rotateLie rotateObjects three three
  kill_x : loop three 0 x=0
  kill_y : loop three 1 y=0
  AD : EdgeCompatible (eval (t 0 2+t 1 2) (t 2 3)) 0 1 0 3 three four
  DE : EdgeCompatible (eval (t 0 1) (t 1 2+t 1 3)) 0 1 3 4 three four
  AB : EdgeCompatible (eval (t 0 1) (t 1 2)) 0 1 0 1 three four
  BC : EdgeCompatible (eval (t 0 1+t 0 2) (t 1 3+t 2 3)) 0 1 1 2 three four
  CE : EdgeCompatible (eval (t 1 2) (t 2 3)) 0 1 2 4 three four

def value (w : Witness) : L := unit w.three 0 1

theorem value_anti (w : Witness) : value w+eval y x (value w)=0 := by
  have h := w.swap.1 0 1
  change unit w.three 1 0=eval y x (value w) at h
  rw [←h]
  simp only [value,unit]
  abel

theorem rotate_squared : rotateLie.comp rotateLie=eval (-x-y) x := by
  apply FreeLieAlgebra.hom_ext
  intro i
  cases i
  · simp [rotateLie,eval,x,y]
  · simp [rotateLie,eval,x,y]
    abel

theorem value_cyclic (w : Witness) :
    value w+eval y (-x-y) (value w)+eval (-x-y) x (value w)=0 := by
  have h₁ := w.rotate.1 0 1
  have h₂ := w.rotate.1 1 2
  change unit w.three 1 2=rotateLie (value w) at h₁
  change unit w.three 2 0=rotateLie (unit w.three 1 2) at h₂
  rw [h₁] at h₂
  have hsq : rotateLie (rotateLie (value w))=eval (-x-y) x (value w) :=
    LieHom.congr_fun rotate_squared (value w)
  rw [hsq] at h₂
  change value w+rotateLie (value w)+eval (-x-y) x (value w)=0
  rw [←h₁,←h₂]
  simp only [value,unit]
  abel

theorem value_pentagon (w : Witness) :
    eval (t 0 1) (t 1 2+t 1 3) (value w)+eval (t 0 2+t 1 2) (t 2 3) (value w)=
      eval (t 1 2) (t 2 3) (value w)+eval (t 0 1+t 0 2) (t 1 3+t 2 3) (value w)+
        eval (t 0 1) (t 1 2) (value w) := by
  unfold value
  rw [←w.AD.1,←w.DE.1,←w.AB.1,←w.BC.1,←w.CE.1]
  simp only [unit]
  abel

theorem value_mem (w : Witness) : value w∈W :=
  ⟨value_anti w,value_cyclic w,value_pentagon w⟩

theorem source_derivation (w : Witness) : loop w.three 0=derivation (value w) := by
  apply derivation_ext
  · simpa only [derivation_apply,D_x] using w.kill_x
  · have h := loop_change w.three 0 1 y
    rw [w.kill_y] at h
    change 0=loop w.three 0 y+⁅value w,y⁆ at h
    simp only [derivation_apply,D_y]
    rw [←lie_skew y (value w)]
    exact eq_neg_of_add_eq_zero_left h.symm

end RealDeligneDrinfeld.CategoricalValues

namespace RealDeligneDrinfeld.KZHomogeneous

section
open DeligneDrinfeld DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.CutoffPrimitiveExtract DeligneDrinfeld.TruncatedWords
attribute [local instance] LieRing.ofAssociativeRing
 def assoc (a b : L) : A ℝ Bool →ₐ[ℝ] A ℝ Bool := lift (fun i => if i then embed b else embed a)
 @[simp] theorem assoc_atom (a b : L) (i : Bool) : assoc a b (atom i)=if i then embed b else embed a := lift_atom _ _
 theorem assoc_embed (a b p : L) : assoc a b (embed p)=embed (eval a b p) := by
  have hh : (assoc a b).toLieHom.comp embed=embed.comp (eval a b) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change assoc a b (embed (FreeLieAlgebra.of ℝ i))=embed (eval a b (FreeLieAlgebra.of ℝ i))
    rw [embed_of,assoc_atom]
    cases i <;> simp [eval]
  exact LieHom.congr_fun hh p
 theorem assoc_homogeneous (a b : L) (ha : a∈Ln 1) (hb : b∈Ln 1) (i : Bool) :
    assoc a b (atom i)∈homogeneous (fun _ => 1) 1 := by
  rw [assoc_atom]
  cases i
  · exact WeightBridge.embed_homogeneous ha
  · exact WeightBridge.embed_homogeneous hb
 theorem piece_natural (N n : ℕ) (hn : n≤N) (f : A ℝ Bool →ₐ[ℝ] A ℝ Bool)
    (g : CutoffDepth.Q ℝ N →ₐ[ℝ] CutoffDepth.Q ℝ N)
    (hf : ∀ i,f (atom i)∈homogeneous (fun _ => 1) 1)
    (hg : ∀ i,g (CutoffDepth.gen N i)=quotient ∅ N (f (atom i))) (u : CutoffDepth.Q ℝ N) :
    TensorProjection.piece n (normalVal N (g u))=f (TensorProjection.piece n (normalVal N u)) := by
  have he : g.comp (quotient ∅ N)=(quotient ∅ N).comp f := by
    apply AssociativeElimination.hom_ext
    exact hg
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (relations (∅:Set (A ℝ Bool)) N) u
  change TensorProjection.piece n (normalVal N (g (quotient ∅ N p)))=
    f (TensorProjection.piece n (normalVal N (quotient ∅ N p)))
  rw [show g (quotient ∅ N p)=quotient ∅ N (f p) from AlgHom.congr_fun he p,
    normalVal_quotient,normalVal_quotient,piece_trunc _ _ hn,piece_trunc _ _ hn]
  exact (algHom_piece f (fun _ => 1) (fun _ => 1) hf n p).symm
 theorem swap_piece (N n : ℕ) (hn : n≤N) (u : CutoffDepth.Q ℝ N) :
    TensorProjection.piece n (normalVal N (KZSwap.swap N u))=
      assoc y x (TensorProjection.piece n (normalVal N u)) := by
  apply piece_natural N n hn _ _ (assoc_homogeneous y x WeightBridge.y_mem WeightBridge.x_mem)
  intro i
  rw [KZSwap.swap_gen,assoc_atom]
  cases i <;> simp only [x,y,embed_of]
  all_goals rfl
 theorem rotate_piece (N n : ℕ) (hn : n≤N) (u : CutoffDepth.Q ℝ N) :
    TensorProjection.piece n (normalVal N (ComplexComparison.realRotate N u))=
      assoc y (-x-y) (TensorProjection.piece n (normalVal N u)) := by
  apply piece_natural N n hn _ _ (assoc_homogeneous y (-x-y) WeightBridge.y_mem
    ((Ln 1).sub_mem ((Ln 1).neg_mem WeightBridge.x_mem) WeightBridge.y_mem))
  intro i
  rw [ComplexComparison.realRotate_gen,assoc_atom]
  cases i
  · simp only [y,embed_of]; rfl
  · change -CutoffDepth.gen N false-CutoffDepth.gen N true=quotient ∅ N (embed (-x-y))
    simp only [map_sub,map_neg,x,y,embed_of]; rfl
 theorem anti (n : ℕ) : q n+eval y x (q n)=0 := by
  apply UniversalEmbedding.injective
  rw [map_add,map_zero,←assoc_embed, q_embed_any n n le_rfl]
  have hh := congrArg (fun u => TensorProjection.piece n (normalVal n u)) (KZSwap.value_swap n)
  rw [swap_piece n n le_rfl,map_neg,map_neg] at hh
  change TensorProjection.piece n (V n)+assoc y x (TensorProjection.piece n (V n))=0
  rw [hh,add_neg_cancel]
 theorem cyclic (n : ℕ) : q n+eval y (-x-y) (q n)+eval (-x-y) x (q n)=0 := by
  have hrot (p : L) : eval y (-x-y) (eval y (-x-y) p)=eval (-x-y) x p :=
    LieHom.congr_fun CategoricalValues.rotate_squared p
  apply UniversalEmbedding.injective
  rw [map_add,map_add,map_zero,←hrot,←assoc_embed,←assoc_embed,←assoc_embed,q_embed_any n n le_rfl]
  have hh := congrArg (fun u => TensorProjection.piece n (normalVal n u)) (ComplexComparison.real_value_cyclic n)
  simpa only [map_add,map_zero,rotate_piece n n le_rfl] using hh
end

open DeligneDrinfeld DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.CutoffPrimitiveExtract DeligneDrinfeld.TruncatedWords
open DeligneDrinfeld.LieGrading DeligneDrinfeld.UniversalEmbedding
 theorem value_depth (N : ℕ) : KZComparison.value N∈CutoffDepth.depthSpace N 1 := by
  have hh := (CutoffDepth.depthSpace N 1).add_mem
    (CutoffDepth.depth_antitone N (by omega : 1≤2) (KZComparison.arrow_log_congruence N))
    (KZComparison.arrow_depth N)
  simpa only [sub_add_cancel] using hh
 theorem normal_depth (N : ℕ) : V N∈above GenericIhara.depth 1 := by
  obtain ⟨p,hp,h⟩ := value_depth N
  change CutoffDepth.quotient N p=KZComparison.value N at h
  rw [V,←h,normalVal_quotient]
  exact project_preserves hp
 theorem q_depth (n : ℕ) : embed (q n)∈above GenericIhara.depth 1 := by
  rw [q_embed_any n n le_rfl]
  exact project_preserves (normal_depth n)
 theorem weight_one_form {p : L} (hp : p∈Ln 1) : ∃ a b : ℝ,p=a • x+b • y := by
  rw [Ln,WeightBridge.piece_eq] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,hu,rfl⟩ := hp
    obtain ⟨a,rfl⟩ := LowWeight.tree_degree_one u hu
    cases a
    · exact ⟨1,0,by simp [Tree.eval,x]⟩
    · exact ⟨0,1,by simp [Tree.eval,y]⟩
  | zero => exact ⟨0,0,by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨a,b,rfl⟩ := hp
    obtain ⟨c,d,rfl⟩ := hq
    exact ⟨a+c,b+d,by simp only [add_smul]; abel⟩
  | smul c p _ hp =>
    obtain ⟨a,b,rfl⟩ := hp
    exact ⟨c*a,c*b,by simp only [smul_add,mul_smul]⟩
 theorem q_one : q 1=0 := by
  classical
  obtain ⟨a,b,h⟩ := weight_one_form (q_homogeneous 1)
  have hd := q_depth 1
  have ha := coeff_support hd (FreeMonoid.of false) (by simp [GenericIhara.depth])
  rw [h,map_add,map_smul,map_smul] at ha
  simp only [MonoidAlgebra.coeff_add,MonoidAlgebra.coeff_smul,x,y,embed_of,atom,MonoidAlgebra.coeff_single] at ha
  norm_num at ha
  change a+Finsupp.single (FreeMonoid.of true) b (FreeMonoid.of false)=0 at ha
  rw [Finsupp.single_eq_of_ne (by intro he; have hh := congrArg FreeMonoid.toList he; simp at hh),add_zero] at ha
  have hs := anti 1
  rw [h,ha,zero_smul,zero_add] at hs
  have hh := congrArg (fun p => MonoidAlgebra.coeff (embed p) (FreeMonoid.of false)) hs
  simp only [map_add,map_smul,map_zero,eval,y,x,FreeLieAlgebra.lift_of_apply,↓reduceIte,embed_of,atom,MonoidAlgebra.coeff_add,MonoidAlgebra.coeff_smul,MonoidAlgebra.coeff_single,MonoidAlgebra.coeff_zero] at hh
  norm_num at hh
  change Finsupp.single (FreeMonoid.of true) b (FreeMonoid.of false)+b=0 at hh
  rw [Finsupp.single_eq_of_ne (by intro he; have hh := congrArg FreeMonoid.toList he; simp at hh),zero_add] at hh
  simp only [h,ha,hh,zero_smul,zero_add]
 def cyc : L →ₗ[ℝ] L := LinearMap.id+(eval y (-x-y)).toLinearMap+(eval (-x-y) x).toLinearMap
 theorem cyclic_weight_two {p : L} (hp : p∈Ln 2) : cyc p=(3 : ℝ) • p := by
  rw [Ln,WeightBridge.piece_eq] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,hu,rfl⟩ := hp
    cases u with
    | leaf a => simp at hu
    | node u v =>
      have h1 := LowWeight.treeDegree_pos (fun _ : Bool => Nat.zero_lt_one) u
      have h2 := LowWeight.treeDegree_pos (fun _ : Bool => Nat.zero_lt_one) v
      simp only [treeDegree_node] at hu
      obtain ⟨a,rfl⟩ := LowWeight.tree_degree_one u (by omega)
      obtain ⟨b,rfl⟩ := LowWeight.tree_degree_one v (by omega)
      cases a <;> cases b <;>
        simp [Tree.eval,cyc,eval,x,y,lie_sub,sub_lie,lie_skew,show (3 : ℝ)=(1+1+1) by norm_num,add_smul]
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add,hp,hq,smul_add]
  | smul c p _ hp => simp only [map_smul,hp,smul_smul,mul_comm]
 theorem q_two : q 2=0 := by
  have hc : cyc (q 2)=0 := cyclic 2
  rw [cyclic_weight_two (q_homogeneous 2)] at hc
  exact (smul_eq_zero.mp hc).resolve_left (by norm_num)
 theorem q_low {n : ℕ} (hn : n≤2) : q n=0 := by
  interval_cases n
  · simp [q]
  · exact q_one
  · exact q_two
end RealDeligneDrinfeld.KZHomogeneous

namespace DeligneDrinfeld.TangentialCutoff

section
open AssociativeElimination WordGrading TruncatedWords
variable {R α : Type*} [CommRing R]
variable (P : Set (A R α)) (N : ℕ)
 variable (d : Module.End R (TruncatedWords.Q P N)) (hd : ∀ a b,d (a*b)=d a*b+a*d b) (h1 : d 1=0)
 include hd h1
 theorem word_mem (k : ℕ) (hv : ∀ a,d (TruncatedDerivation.gen P N a)∈(filtration P N) (k+1)) (w : FreeMonoid α) :
    d (quotient P N (word w))∈(filtration P N) (degree wt w+k) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp only [word_one,map_one,h1]; exact Submodule.zero_mem _
  | of_mul a w ih =>
    rw [word_mul,map_mul,hd,degree_mul,degree_of]
    change _∈(filtration P N) (1+degree wt w+k)
    apply Submodule.add_mem
    · have hw : quotient P N (word w)∈(filtration P N) (degree wt w) := ⟨word w,WordGrading.word_mem w le_rfl,rfl⟩
      simpa only [TruncatedDerivation.gen,word_of,show k+1+degree wt w=1+degree wt w+k by omega] using filtration_mul P N (k+1) _ (hv a) hw
    · simpa only [Nat.add_assoc,wt,TruncatedDerivation.gen,word_of] using
        filtration_mul P N 1 _ (TruncatedDerivation.gen_mem P N a) ih
 theorem mem (k : ℕ) (hv : ∀ a,d (TruncatedDerivation.gen P N a)∈(filtration P N) (k+1))
    (m : ℕ) (a : (TruncatedWords.Q P N)) (ha : a∈(filtration P N) m) : d a∈(filtration P N) (m+k) := by
  obtain ⟨p,hp,rfl⟩ := ha
  exact map_space (d.comp (quotient P N).toLinearMap) _
    (fun w hw => filtration_antitone P N (Nat.add_le_add_right hw k) (word_mem P N d hd h1 k hv w)) hp

end

open AssociativeElimination TruncatedWords
variable {R : Type*} [CommRing R] (N : ℕ)
 theorem difference_mem (d e : Module.End R (TruncatedWords.Q (∅ : Set (A R Bool)) N)) (q r : (TruncatedWords.Q (∅ : Set (A R Bool)) N))
    (hd : ∀ a b,d (a*b)=d a*b+a*d b) (he : ∀ a b,e (a*b)=e a*b+a*e b)
    (hd1 : d 1=0) (he1 : e 1=0) (hdx : d (TruncatedDerivation.gen (∅ : Set (A R Bool)) N false)=0) (hex : e (TruncatedDerivation.gen (∅ : Set (A R Bool)) N false)=0)
    (hdy : d (TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)=(TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)*q-q*(TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)) (hey : e (TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)=(TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)*r-r*(TruncatedDerivation.gen (∅ : Set (A R Bool)) N true))
    (k : ℕ) (hq : q-r∈(filtration (∅ : Set (A R Bool)) N) k) (m : ℕ) (a : (TruncatedWords.Q (∅ : Set (A R Bool)) N)) (ha : a∈(filtration (∅ : Set (A R Bool)) N) m) :
    d a+q*a-(e a+r*a)∈(filtration (∅ : Set (A R Bool)) N) (m+k) := by
  have hm : (d-e) a∈(filtration (∅ : Set (A R Bool)) N) (m+k) := by
    apply mem ∅ N (d-e) (fun a b => ?_) (by simp only [LinearMap.sub_apply,hd1,he1,sub_self])
      k (fun b => ?_) m a ha
    · simp only [LinearMap.sub_apply,hd,he,sub_mul,mul_sub]
      abel
    · cases b
      · simp only [LinearMap.sub_apply,hdx,hex,sub_self,Submodule.zero_mem]
      · change d (TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)-e (TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)∈_
        rw [hdy,hey]
        have hy := TruncatedDerivation.gen_mem (∅:Set (A R Bool)) N true
        have hm1 := filtration_mul ∅ N 1 k hy hq
        have hm2 := filtration_mul ∅ N k 1 hq hy
        have hh : (TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)*(q-r)-(q-r)*(TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)∈(filtration (∅ : Set (A R Bool)) N) (k+1) :=
          ((filtration (∅ : Set (A R Bool)) N) (k+1)).sub_mem (by simpa only [Nat.add_comm 1 k] using hm1) hm2
        convert hh using 1; simp only [mul_sub,sub_mul]; abel
  have hq' : (q-r)*a∈(filtration (∅ : Set (A R Bool)) N) (m+k) := by
    simpa only [Nat.add_comm k m] using filtration_mul ∅ N k m hq ha
  convert ((filtration (∅ : Set (A R Bool)) N) (m+k)).add_mem hm hq' using 1
  simp only [LinearMap.sub_apply,sub_mul]
  abel
end DeligneDrinfeld.TangentialCutoff

namespace DeligneDrinfeld.CutoffCategory
open AssociativeElimination WordGrading TruncatedWords
variable {R α B O O' : Type*} [CommRing R] [Ring B] [Algebra R B]
variable (P : Set (A R α)) (N : ℕ)
variable (g : CategoryExp.Data R (TruncatedWords.Q P N) O) (k : CategoryExp.Data R B O')
  (f : TruncatedWords.Q P N →ₐ[R] B) (p : O) (s : O')

 theorem loop_natural (hgen : ∀ a,k.D s s (f (TruncatedDerivation.gen P N a))=
      f (g.D p p (TruncatedDerivation.gen P N a))) (u : TruncatedWords.Q P N) :
    k.D s s (f u)=f (g.D p p u) := by
  have hword (w : FreeMonoid α) :
      k.D s s (f (quotient P N (word w)))=f (g.D p p (quotient P N (word w))) := by
    induction w using FreeMonoid.inductionOn' with
    | one => rw [word_one,map_one,map_one,g.one,k.one,map_zero]
    | of_mul a w ih =>
      rw [word_mul,word_of,map_mul,map_mul,k.comp,g.comp,map_add,map_mul,map_mul,ih]
      rw [show quotient P N (atom a)=TruncatedDerivation.gen P N a from rfl,hgen]
  obtain ⟨u,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations P N) u
  induction u using MonoidAlgebra.induction_on with
  | of w => exact hword w
  | add u v hu hv => simp only [map_add,hu,hv]
  | smul r u hu => simp only [map_smul,hu]

 theorem edge_natural (q : O) (t : O')
    (hunit : k.D s t 1=f (g.D p q 1))
    (hgen : ∀ a,k.D s s (f (TruncatedDerivation.gen P N a))=
      f (g.D p p (TruncatedDerivation.gen P N a))) (u : TruncatedWords.Q P N) :
    k.D s t (f u)=f (g.D p q u) := by
  have hg := g.comp p p q u 1
  have hk := k.comp s s t (f u) 1
  simp only [one_mul] at hg hk
  rw [hg,hk,map_add,map_mul,hunit,loop_natural P N g k f p s hgen]

 theorem exp_edge [Module ℚ (TruncatedWords.Q P N)] [Module ℚ B]
    (hg : ∀ p q,IsNilpotent (g.D p q)) (hk : ∀ p q,IsNilpotent (k.D p q))
    (q : O) (t : O')
    (hunit : k.D s t 1=f (g.D p q 1))
    (hgen : ∀ a,k.D s s (f (TruncatedDerivation.gen P N a))=
      f (g.D p p (TruncatedDerivation.gen P N a))) (u : TruncatedWords.Q P N) :
    CategoryExp.act k s t (f u)=f (CategoryExp.act g p q u) :=
  OperatorExp.natural _ _ (hg p q) (hk s t) f.toLinearMap
    (edge_natural P N g k f p s q t hunit hgen) u

end DeligneDrinfeld.CutoffCategory

namespace DeligneDrinfeld.PresentedSubstitution
open AssociativeElimination WordGrading TruncatedWords
variable {R α β : Type*} [CommRing R] (P : Set (A R β)) (N : ℕ)
variable (f : α → TruncatedWords.Q P N) (hf : ∀ a,f a∈filtration P N 1)
include hf
 theorem lift_word_mem (w : FreeMonoid α) :
    lift (R:=R) f (word w)∈filtration P N (degree (fun _ => 1) w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa only [word_one,map_one,degree_one] using filtration_one P N
  | of_mul a w ih =>
    rw [word_mul,word_of,map_mul,lift_atom,degree_mul,degree_of]
    exact filtration_mul P N 1 _ (hf a) ih
 theorem lift_mem {n : ℕ} {a : A R α} (ha : a∈above (fun _ => 1) n) :
    lift (R:=R) f a∈filtration P N n :=
  map_space (lift (R:=R) f).toLinearMap _
    (fun w hw => filtration_antitone P N hw (lift_word_mem P N f hf w)) ha
 def subst : TruncatedWords.Q (∅:Set (A R α)) N →ₐ[R] TruncatedWords.Q P N :=
  RingQuot.liftAlgHom R ⟨lift (R:=R) f,by
    rintro p q ⟨rfl,hp⟩
    rcases hp with hp|hp
    · exact False.elim hp
    · simpa only [filtration_terminal,Submodule.mem_bot,map_zero] using lift_mem P N f hf hp⟩
 @[simp] theorem subst_quotient (a : A R α) :
    subst P N f hf (quotient ∅ N a)=lift (R:=R) f a := by
  simp only [subst,quotient,RingQuot.liftAlgHom_mkAlgHom_apply]
 @[simp] theorem subst_gen (a : α) :
    subst P N f hf (TruncatedDerivation.gen ∅ N a)=f a := by
  rw [TruncatedDerivation.gen,subst_quotient,lift_atom]
 theorem subst_mem {n : ℕ} {a : TruncatedWords.Q (∅:Set (A R α)) N}
    (ha : a∈filtration ∅ N n) : subst P N f hf a∈filtration P N n := by
  obtain ⟨a,ha,rfl⟩ := ha
  change subst P N f hf (quotient ∅ N a)∈_
  rw [subst_quotient]
  exact lift_mem P N f hf ha
end DeligneDrinfeld.PresentedSubstitution

namespace DeligneDrinfeld.PresentedCutoff
open AssociativeElimination WordGrading TruncatedWords
variable {R α M : Type*} [CommRing R] [LieRing M] [LieAlgebra R M]
attribute [local instance] LieRing.ofAssociativeRing
variable (P : Set (A R α)) (N : ℕ)
local notation "Q" => TruncatedWords.Q P N

 theorem raw_embed (d : LieDerivation R M M) (e : FreeLieAlgebra R α →ₗ⁅R⁆ M)
    (j : M →ₗ⁅R⁆ Q) (hj : ∀ a,j (e (FreeLieAlgebra.of R a))=TruncatedDerivation.gen P N a)
    (p : FreeLieAlgebra R α) :
    TruncatedDerivation.raw P N (fun a => j (d (e (FreeLieAlgebra.of R a)))) (embed p)=j (d (e p)) := by
  have he : (quotient P N).toLieHom.comp embed=j.comp e := by
    apply FreeLieAlgebra.hom_ext
    intro a
    change quotient P N (embed (FreeLieAlgebra.of R a))=j (e (FreeLieAlgebra.of R a))
    rw [embed_of,hj]; rfl
  have he' (p : FreeLieAlgebra R α) : quotient P N (embed p)=j (e p) := LieHom.congr_fun he p
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => rw [embed_of,TruncatedDerivation.raw_atom]
  | ha a b ha hb => simp only [map_add,ha,hb]
  | hs r a ha => simp only [map_smul,ha]
  | hl a b ha hb =>
    simp only [LieHom.map_lie,LieDerivation.apply_lie_eq_add,map_add]
    change TruncatedDerivation.raw P N _ (embed a*embed b-embed b*embed a)=_
    rw [map_sub,TruncatedDerivation.raw_mul,TruncatedDerivation.raw_mul,ha,hb,he',he']
    simp only [Ring.lie_def]
    noncomm_ring

 theorem derivation_embed (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈filtration P N (k+1))
    (hP : ∀ p∈P,TruncatedDerivation.raw P N v p=0)
    (d : LieDerivation R M M) (e : FreeLieAlgebra R α →ₗ⁅R⁆ M)
    (j : M →ₗ⁅R⁆ Q) (hj : ∀ a,j (e (FreeLieAlgebra.of R a))=TruncatedDerivation.gen P N a)
    (hv' : ∀ a,v a=j (d (e (FreeLieAlgebra.of R a)))) (p : FreeLieAlgebra R α) :
    TruncatedDerivation.derivation P N k v hv hP (quotient P N (embed p))=j (d (e p)) := by
  rw [TruncatedDerivation.derivation_quotient]
  have he : v=(fun a => j (d (e (FreeLieAlgebra.of R a)))) := funext hv'
  rw [he]
  exact raw_embed P N d e j hj p

end DeligneDrinfeld.PresentedCutoff

end

end OAI
