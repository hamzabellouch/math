import OAI.Algebra.Drinfeld.Holonomy

namespace OAI

noncomputable section

namespace DeligneDrinfeld.FourFrames
open FinitePicard KZCollar KZRectangle StraightKZ
attribute [local instance] LieRing.ofAssociativeRing
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
variable (F : NilpotentFiltration A) (j : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ A)
  (hc : ∀ i,chords j i∈F.space 1)

include hc in
theorem corner_reverse (p : Fin 4 → ℝ) (k l : Fin 5) :
    Ring.inverse (Ring.inverse (corner F j p k)*corner F j p l)=
      Ring.inverse (corner F j p l)*corner F j p k := by
  rw [Ring.inverse_mul (Or.inr (corner_isUnit F j hc p l)),
    Ring.inverse_inverse (corner_isUnit F j hc p k)]

include hc in
theorem DE_insertion {p : Fin 4 → ℝ} (hp : StrictMono p) :
    Ring.inverse (corner F j p 4)*corner F j p 3=
      associator F (chords j 0) (chords j 3+chords j 4) := by
  rw [←corner_reverse F j hc p 3 4,ED_insertion F j hc hp,add_comm (chords j 4),
    associator_swap F (hc 0) ((F.space 1).add_mem (hc 3) (hc 4)),
    Ring.inverse_inverse (associator_isUnit F (hc 0) ((F.space 1).add_mem (hc 3) (hc 4)))]

include hc in
theorem CE_insertion {p : Fin 4 → ℝ} (hp : StrictMono p) :
    Ring.inverse (corner F j p 4)*corner F j p 2=associator F (chords j 3) (chords j 5) := by
  rw [←corner_reverse F j hc p 2 4,EC_insertion F j hc hp,
    associator_swap F (hc 3) (hc 5),Ring.inverse_inverse (associator_isUnit F (hc 3) (hc 5))]

include hc in

theorem associator_pentagon :
    associator F (chords j 0) (chords j 3+chords j 4)*
      associator F (chords j 1+chords j 3) (chords j 5)=
    associator F (chords j 3) (chords j 5)*
      associator F (chords j 0+chords j 1) (chords j 4+chords j 5)*
        associator F (chords j 0) (chords j 3) := by
  let p : Fin 4 → ℝ := fun i => (i:ℕ)
  have hp : StrictMono p := by
    intro i k hik
    change ((i:ℕ):ℝ)<((k:ℕ):ℝ)
    exact_mod_cast hik
  rw [←DE_insertion F j hc hp,←AD_insertion F j hc hp,←CE_insertion F j hc hp,
    ←BC_insertion F j hc hp,←AB_insertion F j hc hp,
    corner_cocycle F j hc p 4 3 0,corner_cocycle F j hc p 4 2 1,
    corner_cocycle F j hc p 4 1 0]

end DeligneDrinfeld.FourFrames

namespace RealDeligneDrinfeld.KZBraidPentagon
open DeligneDrinfeld DeligneDrinfeld.FinitePicard DeligneDrinfeld.KZCollar
open BraidInsertionExp T4Basic
attribute [local instance] LieRing.ofAssociativeRing
local instance (N : ℕ) : NormedRing (BraidCutoff.Q N) := FiniteAlgebraNorm.normedRing _
local instance (N : ℕ) : NormedAlgebra ℝ (BraidCutoff.Q N) := FiniteAlgebraNorm.normedAlgebra _
def F (N : ℕ) : NilpotentFiltration (BraidCutoff.Q N) where
  space := BraidCutoff.F N
  antitone := TruncatedWords.filtration_antitone _ N
  one_mem := TruncatedWords.filtration_one _ N
  mul_mem := TruncatedWords.filtration_mul _ N
  cutoff := N
  terminal := TruncatedWords.filtration_terminal _ N

def generic (N : ℕ) (s : ℝ) : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ BraidCutoff.Q N :=
  GenericBraid.lift (fun i j => s • BraidCutoff.lieMap N (t i j))
    (by intro i; rw [t_self,map_zero,smul_zero])
    (by intro i j; rw [t_comm i j])
    (by
      intro i j k l hik hil hjk hjl
      by_cases hij : i=j
      · subst j; rw [t_self,map_zero,smul_zero,zero_lie]
      by_cases hkl : k=l
      · subst l; rw [t_self,map_zero,smul_zero,lie_zero]
      rw [smul_lie,lie_smul,←LieHom.map_lie,t_disjoint i j k l hij hik hil hjk hjl hkl,map_zero,smul_zero,smul_zero])
    (by intro i j k hij hik hjk
        rw [←smul_add,←map_add,smul_lie,lie_smul,←LieHom.map_lie,t_three i j k hij hik hjk,map_zero,smul_zero,smul_zero])
@[simp] theorem generic_t (N : ℕ) (s : ℝ) (i j : Fin 4) :
    generic N s (GenericBraid.t i j)=s • BraidCutoff.lieMap N (t i j) := GenericBraid.lift_t _ _ _ _ _ _ _
theorem chords_mem (N : ℕ) (s : ℝ) (i : Fin 6) : KZRectangle.chords (generic N s) i∈(F N).space 1 := by
  fin_cases i <;> simp only [KZRectangle.chords,generic_t] <;>
    exact Submodule.smul_mem _ s (BraidCutoff.t_mem N _ _)
theorem insert_associator (N : ℕ) (s : ℝ) (X Y : T4) (hX hY) :
    insert N X Y hX hY (associator (CutoffKZ.weight N) (s • CutoffKZ.X N) (s • CutoffKZ.Y N))=
      associator (F N) (s • BraidCutoff.lieMap N X) (s • BraidCutoff.lieMap N Y) := by
  rw [map_associator (insert N X Y hX hY) (CutoffKZ.weight N) (F N) rfl
    (Submodule.smul_mem _ s (CutoffDepth.gen_weight N false))
    (Submodule.smul_mem _ s (CutoffDepth.gen_weight N true)),map_smul,map_smul]
  rw [show insert N X Y hX hY (CutoffKZ.X N)=BraidCutoff.lieMap N X from insert_gen N X Y hX hY false,
    show insert N X Y hX hY (CutoffKZ.Y N)=BraidCutoff.lieMap N Y from insert_gen N X Y hX hY true]
theorem pentagon (N : ℕ) (s : ℝ) :
    let u := associator (CutoffKZ.weight N) (s • CutoffKZ.X N) (s • CutoffKZ.Y N)
    IDE N u*IAD N u=ICE N u*IBC N u*IAB N u := by
  dsimp only
  let u := associator (CutoffKZ.weight N) (s • CutoffKZ.X N) (s • CutoffKZ.Y N)
  have hDE : IDE N u=associator (F N) (s • BraidCutoff.lieMap N a) (s • BraidCutoff.lieMap N (b+e)) := insert_associator N s _ _ _ _
  have hAD : IAD N u=associator (F N) (s • BraidCutoff.lieMap N (d+b)) (s • BraidCutoff.lieMap N c) := insert_associator N s _ _ _ _
  have hCE : ICE N u=associator (F N) (s • BraidCutoff.lieMap N b) (s • BraidCutoff.lieMap N c) := insert_associator N s _ _ _ _
  have hBC : IBC N u=associator (F N) (s • BraidCutoff.lieMap N (a+d)) (s • BraidCutoff.lieMap N (e+c)) := insert_associator N s _ _ _ _
  have hAB : IAB N u=associator (F N) (s • BraidCutoff.lieMap N a) (s • BraidCutoff.lieMap N b) := insert_associator N s _ _ _ _
  change IDE N u*IAD N u=ICE N u*IBC N u*IAB N u
  rw [hDE,hAD,hCE,hBC,hAB]
  have hh := FourFrames.associator_pentagon (F N) (generic N s) (chords_mem N s)
  simpa [KZRectangle.chords,KZRectangle.edges,smul_add,a,b,c,d,e] using hh
 theorem positive (N : ℕ) : IDE N (KZComparison.positive N)*IAD N (KZComparison.positive N)=
    ICE N (KZComparison.positive N)*IBC N (KZComparison.positive N)*IAB N (KZComparison.positive N) := by
  simpa only [one_smul,KZComparison.positive_val] using pentagon N 1
 theorem negative (N : ℕ) : IDE N (KZComparison.negative N)*IAD N (KZComparison.negative N)=
    ICE N (KZComparison.negative N)*IBC N (KZComparison.negative N)*IAB N (KZComparison.negative N) := by
  simpa only [neg_one_smul,KZComparison.negative_val] using pentagon N (-1)
end RealDeligneDrinfeld.KZBraidPentagon

namespace DeligneDrinfeld.EulerPBW
variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
attribute [local instance] LieRing.ofAssociativeRing

def affine (D : LieDerivation R L L) (a : L) : Module.End R (L × R) where
  toFun v := (⁅a,v.1⁆+v.2 • D a,0)
  map_add' v w := by ext <;> simp only [Prod.fst_add,Prod.snd_add,lie_add,add_smul] <;> abel
  map_smul' c v := by
    apply Prod.ext
    · change ⁅a,c • v.1⁆+(c*v.2) • D a=c • (⁅a,v.1⁆+v.2 • D a)
      rw [lie_smul,smul_add,smul_smul]
    · change (0:R)=c*0
      exact (mul_zero c).symm

@[simp] theorem affine_apply (D : LieDerivation R L L) (a v : L) (c : R) :
    affine D a (v,c)=(⁅a,v⁆+c • D a,0) := rfl

def affineHom (D : LieDerivation R L L) : L →ₗ⁅R⁆ Module.End R (L × R) where
  toFun := affine D
  map_add' a b := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · change ⁅a+b,v.1⁆+v.2 • D (a+b)=(⁅a,v.1⁆+v.2 • D a)+(⁅b,v.1⁆+v.2 • D b)
      rw [add_lie,map_add,smul_add]
      abel
    · change (0:R)=0+0
      exact (add_zero _).symm
  map_smul' c a := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · change ⁅c • a,v.1⁆+v.2 • D (c • a)=c • (⁅a,v.1⁆+v.2 • D a)
      rw [smul_lie,map_smul,smul_add,smul_comm v.2 c]
    · change (0:R)=c*0
      exact (mul_zero c).symm
  map_lie' := by
    intro a b
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · change ⁅⁅a,b⁆,v.1⁆+v.2 • D ⁅a,b⁆=
        (⁅a,⁅b,v.1⁆+v.2 • D b⁆+0 • D a)-(⁅b,⁅a,v.1⁆+v.2 • D a⁆+0 • D b)
      simp only [zero_smul,add_zero,LieDerivation.apply_lie_eq_add,smul_add,lie_add,lie_smul]
      rw [lie_lie,←lie_skew (D a) b,smul_neg]
      abel
    · change (0:R)=0-0
      exact (sub_self _).symm

def dynkin (D : LieDerivation R L L) : UniversalEnvelopingAlgebra R L →ₗ[R] L :=
  (LinearMap.fst R L R).comp ((LinearMap.applyₗ (R:=R) (0,1)).comp
    (UniversalEnvelopingAlgebra.lift R (affineHom D)).toLinearMap)

@[simp] theorem dynkin_iota (D : LieDerivation R L L) (a : L) :
    dynkin D (UniversalEnvelopingAlgebra.ι R a)=D a := by
  change (UniversalEnvelopingAlgebra.lift R (affineHom D)
    (UniversalEnvelopingAlgebra.ι R a) (0,1)).1=D a
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  simp [affineHom,affine]

theorem injective_iota (D : LieDerivation R L L) (hD : Function.Injective D) :
    Function.Injective (UniversalEnvelopingAlgebra.ι R (L:=L)) := by
  intro a b h
  apply hD
  simpa only [dynkin_iota] using congrArg (dynkin D) h

end DeligneDrinfeld.EulerPBW

namespace DeligneDrinfeld.LieCutoffFaithful
open AssociativeElimination WordGrading TruncatedWords TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α M : Type*} [CommRing R] [LieRing M] [LieAlgebra R M]
abbrev S (R : Type*) [CommRing R] (N : ℕ) := TruncatedWords.Q (∅ : Set (A R Unit)) N

def z (N : ℕ) : S R N := quotient ∅ N (atom ())

 theorem z_pow (N n : ℕ) : (z (R:=R) N)^n=quotient ∅ N (word ((FreeMonoid.of ())^n)) := by
  induction n with
  | zero => simp only [pow_zero,word_one,map_one]
  | succ n ih => rw [pow_succ,pow_succ,word_mul,map_mul,←ih,word_of]; rfl
 theorem z_pow_zero {N n : ℕ} (hn : N<n) : (z (R:=R) N)^n=0 := by
  rw [z_pow]
  apply quotient_above ∅ N
  apply word_mem
  have hd : degree (wt : Unit → ℕ) ((FreeMonoid.of ())^n)=n := by
    clear hn
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,degree_mul,ih,degree_of]
  rw [hd]
  omega

variable {B : Type*} [Ring B] [Algebra R B]
def lift (N : ℕ) (g : α → B) : A R α →ₐ[R] (S R N ⊗[R] B) :=
  AssociativeElimination.lift (R:=R) (B:=S R N ⊗[R] B) (fun a => z N ⊗ₜ[R] g a)

 @[simp] theorem lift_atom (N : ℕ) (g : α → B) (a : α) : lift (R:=R) N g (atom a)=z N ⊗ₜ[R] g a := by
  unfold lift
  exact AssociativeElimination.lift_atom (R:=R) (B:=S R N ⊗[R] B) _ a

 theorem lift_word (N : ℕ) (g : α → B) (w : FreeMonoid α) :
    lift N g (word w)=(z (R:=R) N ^ (degree wt w)) ⊗ₜ[R] AssociativeElimination.lift (R:=R) g (word w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp only [word_one,map_one,degree_one,pow_zero,Algebra.TensorProduct.one_def]
  | of_mul a w ih =>
    simp only [word_mul,word_of,map_mul,lift_atom,AssociativeElimination.lift_atom,ih,degree_mul,degree_of]
    rw [Algebra.TensorProduct.tmul_mul_tmul,←pow_succ']
    simp only [wt,Nat.add_comm 1]

 theorem lift_above (N : ℕ) (g : α → B) {p : A R α} (hp : p∈above wt (N+1)) : lift N g p=0 := by
  have hh : lift N g p∈(⊥ : Submodule R (_)) := map_space (lift N g).toLinearMap _ (fun w hw => by
    change lift N g (word w)=0
    rw [lift_word,z_pow_zero (by omega),zero_tmul]) hp
  exact hh

variable [Algebra ℝ B]

 theorem lift_weight {wtL : α → ℕ} (hwt : ∀ a,wtL a=1) (N : ℕ) (g : α → B)
    {n : ℕ} {p : FreeLieAlgebra ℝ α}
    (hp : RealDeligneDrinfeld.WeightedWord wtL n p) :
    lift (R:=ℝ) N g (embed p)=(z (R:=ℝ) N ^ n) ⊗ₜ[ℝ] FreeLieAlgebra.lift ℝ g p := by
  induction hp with
  | generator a =>
    rw [embed_of]
    simp only [LieCutoffFaithful.lift,AssociativeElimination.lift_atom,FreeLieAlgebra.lift_of_apply,hwt,pow_one]
  | @bracket n m a b ha hb ia ib =>
    rw [LieHom.map_lie]
    change lift (R:=ℝ) N g (embed _*embed _-embed _*embed _)=_
    rw [map_sub,map_mul,map_mul,ia,ib,Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul,←pow_add,←pow_add,Nat.add_comm m n]
    rw [←tmul_sub,LieHom.map_lie,Ring.lie_def]

 theorem lift_piece (N : ℕ) (g : α → B) {n : ℕ} {p : FreeLieAlgebra ℝ α}
    (hp : p∈RealDeligneDrinfeld.weightPiece (fun _ : α => 1) n) :
    lift (R:=ℝ) N g (embed p)=(z (R:=ℝ) N ^ n) ⊗ₜ[ℝ] FreeLieAlgebra.lift ℝ g p := by
  apply Submodule.span_induction (p:=fun p _ => lift (R:=ℝ) N g (embed p)=
    (z (R:=ℝ) N ^ n) ⊗ₜ[ℝ] FreeLieAlgebra.lift ℝ g p) ?_ ?_ ?_ ?_ hp
  · intro p hp; exact lift_weight (fun _ => rfl) N g hp
  · simp only [map_zero,tmul_zero]
  · intro p q _ _ hp hq; simp only [map_add,hp,hq,tmul_add]
  · intro s p _ hp; simp only [map_smul,hp,tmul_smul]

 theorem coefficient_z_pow {N n : ℕ} (hn : n≤N) :
    TruncatedFree.coefficient N ((FreeMonoid.of ())^n) (z (R:=ℝ) N ^ n)=1 := by
  rw [z_pow,TruncatedFree.coefficient_quotient]
  have hd : degree (wt : Unit → ℕ) ((FreeMonoid.of ())^n)=n := by
    clear hn
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,degree_mul,ih,degree_of]
  simp only [hd,ite_eq_left hn,word,MonoidAlgebra.coeff_single,Finsupp.single_eq_same]

 def extract (N n : ℕ) : S ℝ N ⊗[ℝ] B →ₗ[ℝ] B :=
  (TensorProduct.lid ℝ B).toLinearMap.comp
    (TensorProduct.map (TruncatedFree.coefficient N ((FreeMonoid.of ())^n)) (LinearMap.id))

 theorem extract_tmul {N n : ℕ} (hn : n≤N) (b : B) :
    extract N n ((z (R:=ℝ) N ^ n) ⊗ₜ[ℝ] b)=b := by
  change TruncatedFree.coefficient N ((FreeMonoid.of ())^n) (z (R:=ℝ) N ^ n) • b=b
  rw [coefficient_z_pow hn,one_smul]

end DeligneDrinfeld.LieCutoffFaithful

namespace RealDeligneDrinfeld.AffineWeight
variable {M : Type*} [LieRing M] [LieAlgebra ℝ M]
attribute [local instance] LieRing.ofAssociativeRing

def op (a b : M) : Module.End ℝ (M × ℝ) where
  toFun v := (⁅a,v.1⁆+v.2 • b,0)
  map_add' v w := by ext <;> simp only [Prod.fst_add,Prod.snd_add,lie_add,add_smul] <;> abel
  map_smul' c v := by
    apply Prod.ext
    · change ⁅a,c • v.1⁆+(c*v.2) • b=c • (⁅a,v.1⁆+v.2 • b)
      rw [lie_smul,smul_add,smul_smul]
    · change (0:ℝ)=c*0
      exact (mul_zero c).symm

 theorem op_lie (a b c d : M) : ⁅op a b,op c d⁆=op ⁅a,c⁆ (⁅b,c⁆+⁅a,d⁆) := by
  apply LinearMap.ext
  intro v
  apply Prod.ext
  · change (⁅a,⁅c,v.1⁆+v.2 • d⁆+0 • b)-(⁅c,⁅a,v.1⁆+v.2 • b⁆+0 • d)=
      ⁅⁅a,c⁆,v.1⁆+v.2 • (⁅b,c⁆+⁅a,d⁆)
    simp only [zero_smul,add_zero,smul_add,lie_add,lie_smul]
    rw [lie_lie,←lie_skew b c,smul_neg]
    abel
  · change (0:ℝ)-0=0
    exact sub_self _

 def homogeneous (n : ℕ) : M →ₗ[ℝ] Module.End ℝ (M×ℝ) where
  toFun a := op a ((n:ℝ) • a)
  map_add' a b := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · change ⁅a+b,v.1⁆+v.2 • ((n:ℝ) • (a+b))=
        (⁅a,v.1⁆+v.2 • ((n:ℝ) • a))+(⁅b,v.1⁆+v.2 • ((n:ℝ) • b))
      simp only [add_lie,smul_add]; abel
    · change (0:ℝ)=0+0; simp
  map_smul' s a := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · change ⁅s • a,v.1⁆+v.2 • ((n:ℝ) • (s • a))=s • (⁅a,v.1⁆+v.2 • ((n:ℝ) • a))
      rw [smul_lie,smul_add,smul_comm (n:ℝ) s,smul_comm v.2 s]
    · change (0:ℝ)=s*0; simp

 theorem homogeneous_lie (n m : ℕ) (a b : M) :
    homogeneous (n+m) ⁅a,b⁆=⁅homogeneous n a,homogeneous m b⁆ := by
  change op ⁅a,b⁆ (((n+m:ℕ):ℝ) • ⁅a,b⁆)=⁅op a ((n:ℝ) • a),op b ((m:ℝ) • b)⁆
  rw [op_lie,smul_lie,lie_smul,Nat.cast_add,add_smul]

 variable {α : Type*}
 def representation (f : α → M) : FreeLieAlgebra ℝ α →ₗ⁅ℝ⁆ Module.End ℝ (M×ℝ) :=
  FreeLieAlgebra.lift ℝ (fun a => homogeneous 1 (f a))

 theorem word_rep (f : α → M) {n : ℕ} {p : FreeLieAlgebra ℝ α}
    (hp : WeightedWord (fun _ : α => 1) n p) :
    representation f p=homogeneous n (FreeLieAlgebra.lift ℝ f p) := by
  induction hp with
  | generator a => simp only [representation,FreeLieAlgebra.lift_of_apply]
  | bracket ha hb ia ib => rw [LieHom.map_lie,ia,ib,LieHom.map_lie,homogeneous_lie]

 theorem weight_rep (f : α → M) {n : ℕ} {p : FreeLieAlgebra ℝ α}
    (hp : p∈weightPiece (fun _ : α => 1) n) :
    representation f p=homogeneous n (FreeLieAlgebra.lift ℝ f p) := by
  apply Submodule.span_induction (p:=fun p _ => representation f p=homogeneous n (FreeLieAlgebra.lift ℝ f p)) ?_ ?_ ?_ ?_ hp
  · intro p hp; exact word_rep f hp
  · simp only [map_zero]
  · intro p q _ _ hp hq; simp only [map_add,hp,hq]
  · intro s p _ hp; simp only [map_smul,hp]

 theorem homogeneous_injective {n : ℕ} (hn : 0<n) : Function.Injective (homogeneous (M:=M) n) := by
  intro p q h
  have hh := congrArg (fun (F : Module.End ℝ (M×ℝ)) => (F (0,1)).1) h
  change ⁅p,0⁆+(1:ℝ) • ((n:ℝ) • p)=⁅q,0⁆+(1:ℝ) • ((n:ℝ) • q) at hh
  simp only [lie_zero,one_smul,zero_add] at hh
  exact (smul_right_injective M (by exact_mod_cast (Nat.ne_of_gt hn) : (n:ℝ)≠0)) hh

end RealDeligneDrinfeld.AffineWeight

namespace RealDeligneDrinfeld.BraidCutoff
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.TruncatedWords DeligneDrinfeld.LieCutoffFaithful
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
abbrev Piece (n : ℕ) := weightPiece (fun _ : Edge => 1) n
 theorem of_mem (a : Edge) : FreeLieAlgebra.of ℝ a∈Piece 1 :=
  Submodule.subset_span (WeightedWord.generator _)
 theorem chord_mem (i j : Fin 4) : chord i j∈Piece 1 := by
  unfold chord
  split_ifs
  · exact of_mem _
  · exact of_mem _
  · exact Submodule.zero_mem _
 theorem piece_lie {n m : ℕ} {a b : BraidFree} (ha : a∈Piece n) (hb : b∈Piece m) : ⁅a,b⁆∈Piece (n+m) := by
  apply Submodule.span_induction (p:=fun a _ => ⁅a,b⁆∈Piece (n+m)) ?_ ?_ ?_ ?_ ha
  · intro a ha
    apply Submodule.span_induction (p:=fun b _ => ⁅a,b⁆∈Piece (n+m)) ?_ ?_ ?_ ?_ hb
    · intro b hb; exact Submodule.subset_span (WeightedWord.bracket ha hb)
    · rw [lie_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [lie_add]; exact Submodule.add_mem _ ha hb
    · intro s b _ hb; rw [lie_smul]; exact Submodule.smul_mem _ s hb
  · rw [zero_lie]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [add_lie]; exact Submodule.add_mem _ ha hb
  · intro s a _ ha; rw [smul_lie]; exact Submodule.smul_mem _ s ha
 theorem relation_piece {p : BraidFree} (hp : p∈braidRelations) : p∈Piece 2 := by
  rcases hp with ⟨i,j,k,l,_,_,_,_,_,_,rfl⟩|⟨i,j,k,_,_,_,rfl⟩
  · exact piece_lie (n:=1) (m:=1) (chord_mem i j) (chord_mem k l)
  · exact piece_lie (n:=1) (m:=1) (chord_mem i j) ((Piece 1).add_mem (chord_mem i k) (chord_mem j k))

 def affineGenerators (a : Edge) : Module.End ℝ (T4×ℝ) := AffineWeight.homogeneous 1 (projection (FreeLieAlgebra.of ℝ a))
 theorem projection_eq : FreeLieAlgebra.lift ℝ (fun a : Edge => projection (FreeLieAlgebra.of ℝ a))=projection := by
  apply FreeLieAlgebra.hom_ext
  intro a
  exact FreeLieAlgebra.lift_of_apply _ a
 theorem affine_weight {n : ℕ} {p : BraidFree} (hp : p∈Piece n) :
    FreeLieAlgebra.lift ℝ affineGenerators p=AffineWeight.homogeneous n (projection p) := by
  have hh := AffineWeight.weight_rep (fun a : Edge => projection (FreeLieAlgebra.of ℝ a)) hp
  rw [projection_eq] at hh
  exact hh

 def representation (N : ℕ) : Q N →ₐ[ℝ] (DeligneDrinfeld.LieCutoffFaithful.S ℝ N ⊗[ℝ] Module.End ℝ (T4×ℝ)) :=
  RingQuot.liftAlgHom ℝ ⟨DeligneDrinfeld.LieCutoffFaithful.lift N affineGenerators,by
    rintro p q ⟨rfl,hp⟩
    rw [map_zero]
    rcases hp with ⟨p,hp,rfl⟩|hp
    · rw [lift_piece N affineGenerators (relation_piece hp),affine_weight (relation_piece hp),projection_relation hp,map_zero,TensorProduct.tmul_zero]
    · exact lift_above N affineGenerators hp⟩

 theorem representation_quotient (N : ℕ) (p : DeligneDrinfeld.AssociativeElimination.A ℝ Edge) :
    representation N (quotient presentation N p)=DeligneDrinfeld.LieCutoffFaithful.lift N affineGenerators p := by
  simp only [representation,quotient,RingQuot.liftAlgHom_mkAlgHom_apply]

 theorem detect {N n : ℕ} (hn : 0<n) (hN : n≤N) {p : BraidFree} (hp : p∈Piece n)
    (hz : lieMap N (projection p)=0) : projection p=0 := by
  have hh := congrArg (representation N) hz
  change representation N (quotient presentation N (embed p))=representation N 0 at hh
  rw [representation_quotient,map_zero,lift_piece N affineGenerators hp,affine_weight hp] at hh
  have hg := congrArg (DeligneDrinfeld.LieCutoffFaithful.extract N n) hh
  rw [extract_tmul hN,map_zero] at hg
  exact AffineWeight.homogeneous_injective hn (by simpa only [map_zero] using hg)

end RealDeligneDrinfeld.BraidCutoff

section
namespace DeligneDrinfeld.TopDifference
open AssociativeElimination TruncatedWords
variable {R α : Type*} [CommRing R] (P : Set (A R α)) (N : ℕ)
 theorem product_zero {u v : Q P N} (hu : u∈filtration P N N) (hv : v∈filtration P N 1) : u*v=0 := by
  have hh := filtration_mul P N N 1 hu hv
  rwa [filtration_terminal,Submodule.mem_bot] at hh
 theorem reverse_zero {u v : Q P N} (hu : u∈filtration P N 1) (hv : v∈filtration P N N) : u*v=0 := by
  have hh := filtration_mul P N 1 N hu hv
  rwa [Nat.add_comm 1 N,filtration_terminal,Submodule.mem_bot] at hh
 theorem product {a a' b b' : Q P N}
    (ha : a-1∈filtration P N 1) (hb' : b'-1∈filtration P N 1)
    (ha' : a'-a∈filtration P N N) (hb : b'-b∈filtration P N N) :
    a'*b'-a*b=(a'-a)+(b'-b) := by
  have h₁ := product_zero P N ha' hb'
  have h₂ := reverse_zero P N ha hb
  have hh : a'*b'-a*b-((a'-a)+(b'-b))=(a'-a)*(b'-1)+(a-1)*(b'-b) := by
    simp only [sub_mul,mul_sub,mul_one,one_mul]; abel
  apply sub_eq_zero.mp
  rw [hh,h₁,h₂,add_zero]
 theorem normalized_product {a b : Q P N}
    (ha : a-1∈filtration P N 1) (hb : b-1∈filtration P N 1) :
    a*b-1∈filtration P N 1 := by
  have ha0 : a∈filtration P N 0 := by
    obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations P N) a
    exact ⟨p,TruncatedFree.all_ge_zero p,rfl⟩
  have hh := filtration_mul P N 0 1 ha0 hb
  convert (filtration P N 1).add_mem hh ha using 1
  simp only [mul_sub,mul_one]; abel
 theorem triple {a a' b b' c c' : Q P N}
    (ha : a-1∈filtration P N 1) (hb : b-1∈filtration P N 1)
    (hb' : b'-1∈filtration P N 1) (hc' : c'-1∈filtration P N 1)
    (hd₁ : a'-a∈filtration P N N) (hd₂ : b'-b∈filtration P N N)
    (hd₃ : c'-c∈filtration P N N) :
    a'*b'*c'-a*b*c=(a'-a)+(b'-b)+(c'-c) := by
  have hh := product P N ha hb' hd₁ hd₂
  have hd : a'*b'-a*b∈filtration P N N := by rw [hh]; exact Submodule.add_mem _ hd₁ hd₂
  rw [product P N (normalized_product P N ha hb) hc' hd hd₃,hh]
end DeligneDrinfeld.TopDifference

namespace RealDeligneDrinfeld.BraidInsertionExp
open DeligneDrinfeld.TruncatedWords
 theorem insert_mem (N : ℕ) (X Y : T4) (hX hY) {n : ℕ} {a : FreeCutoffCategory.Q N}
    (ha : a∈FreeCutoffCategory.F N n) : insert N X Y hX hY a∈BraidCutoff.F N n :=
  DeligneDrinfeld.PresentedSubstitution.subst_mem _ _ _ _ ha
 theorem linear_pentagon_difference (N : ℕ) (u v : FreeCutoffCategory.Q N)
    (hu : u-1∈FreeCutoffCategory.F N 1) (hv : v-1∈FreeCutoffCategory.F N 1)
    (hd : v-u∈FreeCutoffCategory.F N N)
    (hpu : IDE N u*IAD N u=ICE N u*IBC N u*IAB N u)
    (hpv : IDE N v*IAD N v=ICE N v*IBC N v*IAB N v) :
    IDE N (v-u)+IAD N (v-u)=ICE N (v-u)+IBC N (v-u)+IAB N (v-u) := by
  have normal (X Y : T4) (hX hY) (a : FreeCutoffCategory.Q N) (ha : a-1∈FreeCutoffCategory.F N 1) :
      insert N X Y hX hY a-1∈BraidCutoff.F N 1 := by
    simpa only [map_sub,map_one] using insert_mem N X Y hX hY ha
  have diff (X Y : T4) (hX hY) : insert N X Y hX hY v-insert N X Y hX hY u∈BraidCutoff.F N N := by
    simpa only [map_sub] using insert_mem N X Y hX hY hd
  have nd : IDE N u-1∈BraidCutoff.F N 1 := normal _ _ _ _ u hu
  have na : IAD N v-1∈BraidCutoff.F N 1 := normal _ _ _ _ v hv
  have nc : ICE N u-1∈BraidCutoff.F N 1 := normal _ _ _ _ u hu
  have nb : IBC N u-1∈BraidCutoff.F N 1 := normal _ _ _ _ u hu
  have nb' : IBC N v-1∈BraidCutoff.F N 1 := normal _ _ _ _ v hv
  have nab : IAB N v-1∈BraidCutoff.F N 1 := normal _ _ _ _ v hv
  have dd : IDE N v-IDE N u∈BraidCutoff.F N N := diff _ _ _ _
  have da : IAD N v-IAD N u∈BraidCutoff.F N N := diff _ _ _ _
  have dc : ICE N v-ICE N u∈BraidCutoff.F N N := diff _ _ _ _
  have db : IBC N v-IBC N u∈BraidCutoff.F N N := diff _ _ _ _
  have dab : IAB N v-IAB N u∈BraidCutoff.F N N := diff _ _ _ _
  have h₂ := DeligneDrinfeld.TopDifference.product BraidCutoff.presentation N nd na dd da
  have h₃ := DeligneDrinfeld.TopDifference.triple BraidCutoff.presentation N nc nb nb' nab dc db dab
  simp only [map_sub]
  rw [←h₂,←h₃,hpu,hpv]
end RealDeligneDrinfeld.BraidInsertionExp

end

namespace RealDeligneDrinfeld.PentagonDetect
open BraidCutoff BraidInsertionExp
 def value (p : L) : BraidFree :=
  eval (chord 0 1) (chord 1 2+chord 1 3) p+eval (chord 0 2+chord 1 2) (chord 2 3) p-
    (eval (chord 1 2) (chord 2 3) p+eval (chord 0 1+chord 0 2) (chord 1 3+chord 2 3) p+
      eval (chord 0 1) (chord 1 2) p)
 theorem eval_mem {n : ℕ} {p : L} (hp : p∈Ln n) {a b : BraidFree} (ha : a∈Piece 1) (hb : b∈Piece 1) :
    eval a b p∈Piece n := by
  apply WeightBridge.map_mem (eval a b) (fun _ => 1) (fun _ => 1) _ hp
  intro i
  cases i
  · simpa only [eval,FreeLieAlgebra.lift_of_apply,Bool.false_eq_true,↓reduceIte] using ha
  · simpa only [eval,FreeLieAlgebra.lift_of_apply,↓reduceIte] using hb
 theorem homogeneous {n : ℕ} {p : L} (hp : p∈Ln n) : value p∈Piece n := by
  apply (Piece n).sub_mem
  · exact (Piece n).add_mem (eval_mem hp (chord_mem _ _) ((Piece 1).add_mem (chord_mem _ _) (chord_mem _ _)))
      (eval_mem hp ((Piece 1).add_mem (chord_mem _ _) (chord_mem _ _)) (chord_mem _ _))
  · exact (Piece n).add_mem ((Piece n).add_mem (eval_mem hp (chord_mem _ _) (chord_mem _ _))
      (eval_mem hp ((Piece 1).add_mem (chord_mem _ _) (chord_mem _ _)) ((Piece 1).add_mem (chord_mem _ _) (chord_mem _ _))))
      (eval_mem hp (chord_mem _ _) (chord_mem _ _))
 theorem projection_chord (i j : Fin 4) : projection (chord i j)=t i j := rfl
 theorem projection_eval (a b : BraidFree) (p : L) : projection (eval a b p)=eval (projection a) (projection b) p := by
  have he : projection.comp (eval a b)=eval (projection a) (projection b) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [eval]
  exact LieHom.congr_fun he p
 theorem detect {n : ℕ} (hn : 0<n) {p : L} (hp : p∈Ln n)
    (he : IDE n (FreeCutoffCategory.j n p)+IAD n (FreeCutoffCategory.j n p)=
      ICE n (FreeCutoffCategory.j n p)+IBC n (FreeCutoffCategory.j n p)+IAB n (FreeCutoffCategory.j n p)) :
    eval (t 0 1) (t 1 2+t 1 3) p+eval (t 0 2+t 1 2) (t 2 3) p=
      eval (t 1 2) (t 2 3) p+eval (t 0 1+t 0 2) (t 1 3+t 2 3) p+eval (t 0 1) (t 1 2) p := by
  have hh : lieMap n (projection (value p))=0 := by
    simp only [value,map_sub,map_add,projection_eval,projection_chord]
    simpa only [sub_eq_zero,IAB,IAD,IDE,IBC,ICE,insert_j,T4Basic.a,T4Basic.b,T4Basic.c,T4Basic.d,T4Basic.e] using he
  have hz := BraidCutoff.detect hn le_rfl (homogeneous hp) hh
  simpa only [value,map_sub,map_add,projection_eval,projection_chord,sub_eq_zero] using hz
end RealDeligneDrinfeld.PentagonDetect

namespace RealDeligneDrinfeld.KZHomogeneous
open DeligneDrinfeld DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.CutoffPrimitiveExtract DeligneDrinfeld.TruncatedWords
open BraidInsertionExp
 theorem value_sum (N : ℕ) : KZComparison.value N=FreeCutoffCategory.j N (∑ i∈Finset.range (N+1),q i) := by
  have hz := quotient_above (∅:Set (A ℝ Bool)) N (residual_above N (N+1) le_rfl)
  rw [map_sub,map_sum,quotient_normal] at hz
  rw [map_sum]
  exact sub_eq_zero.mp hz
 theorem residual_top (N : ℕ) : KZComparison.value N-FreeCutoffCategory.j N (∑ i∈Finset.range N,q i)=
    FreeCutoffCategory.j N (q N) := by
  rw [value_sum,Finset.sum_range_succ,map_add,add_sub_cancel_left]
 theorem coefficient_solution (N : ℕ) : q N∈W := by
  induction N using Nat.strong_induction_on with | h N ih =>
    by_cases hN : N≤2
    · rw [q_low hN]; exact Submodule.zero_mem _
    have hN' : 2<N := by omega
    let ns : Fin N → ℕ := fun (i : Fin N) => if 2 < i.val then i.val else 3
    have hn : ∀ i,2<ns i := by intro i; dsimp [ns]; split_ifs <;> omega
    have hqn : ∀ i : Fin N,q i.val∈Ln (ns i) := by
      intro i
      dsimp [ns]
      split_ifs with hi
      · exact q_homogeneous _
      · rw [q_low (by omega)]; exact Submodule.zero_mem _
    have hq : ∀ i : Fin N,q i.val∈W := fun i => ih i.val i.isLt
    have hsum : (∑ i : Fin N,q i.val)=∑ i∈Finset.range N,q i := Fin.sum_univ_eq_sum_range q N
    let g := BraidInsertionSum.free N Finset.univ (fun i : Fin N => q i.val) ns hqn
    let u := CategoryExp.act g 0 1 (KZComparison.positive N)
    have hd : KZComparison.value N-FreeCutoffCategory.j N (∑ i : Fin N,q i.val)=FreeCutoffCategory.j N (q N) := by
      rw [hsum,residual_top]
    have hj := FreeCutoffCategory.j_mem (N:=N) (q_homogeneous N)
    have hex := KZLogDifference.exponential N Finset.univ (fun i : Fin N => q i.val) ns hqn hn N (by rw [hd]; exact hj)
    change _ ∈filtration (∅:Set (A ℝ Bool)) N (N+1) at hex
    rw [filtration_terminal,Submodule.mem_bot,hd] at hex
    have hdiff : (KZComparison.negative N:FreeCutoffCategory.Q N)-u=FreeCutoffCategory.j N (q N) := sub_eq_zero.mp hex
    have hp := BraidInsertionSum.pentagon N Finset.univ (fun i : Fin N => q i.val) ns hq hqn hn _ (KZBraidPentagon.positive N)
    have hu : u-1∈FreeCutoffCategory.F N 1 := by
      have hr := BraidInsertionSum.free_raises N Finset.univ (fun i : Fin N => q i.val) ns hqn hn 0 1
      have hh := CategoryExp.unit_leading (CutoffCategory.filtration ∅ N) (g.D 0 1) 1 hr (by omega)
        (filtration_one ∅ N) (KZComparison.positive_weight N)
      have hd1 := hr 0 1 (filtration_one ∅ N)
      have hh' := filtration_antitone (∅:Set (A ℝ Bool)) N (by omega : 1≤1+1) hh
      have hz := (FreeCutoffCategory.F N 1).add_mem ((FreeCutoffCategory.F N 1).add_mem hh' hd1) (KZComparison.positive_weight N)
      convert hz using 1
      dsimp [u,CategoryExp.act]
      abel
    have hh := linear_pentagon_difference N u (KZComparison.negative N) hu (KZComparison.negative_weight N)
      (by rw [hdiff]; exact hj) hp (KZBraidPentagon.negative N)
    rw [hdiff] at hh
    exact ⟨anti N,cyclic N,PentagonDetect.detect (by omega) (q_homogeneous N) hh⟩
end RealDeligneDrinfeld.KZHomogeneous

end

end OAI
