import OAI.Algebra.Drinfeld.RealLie

namespace OAI

noncomputable section

namespace RealDeligneDrinfeld.WeightBridge
open DeligneDrinfeld.LieGrading DeligneDrinfeld.UniversalEmbedding
variable {α : Type*}
 theorem tree_word (wt : α → ℕ) (t : DeligneDrinfeld.UniversalEmbedding.Tree α) : WeightedWord wt (treeDegree wt t) (t.eval : FreeLieAlgebra ℝ α) := by
  induction t with
  | leaf a => simpa only [DeligneDrinfeld.UniversalEmbedding.Tree.eval,treeDegree_leaf] using WeightedWord.generator (wt:=wt) a
  | node a b ha hb => simpa only [DeligneDrinfeld.UniversalEmbedding.Tree.eval,treeDegree_node] using WeightedWord.bracket ha hb

 theorem word_tree {wt : α → ℕ} {n : ℕ} {p : FreeLieAlgebra ℝ α} (hp : WeightedWord wt n p) :
    ∃ t : DeligneDrinfeld.UniversalEmbedding.Tree α,treeDegree wt t=n ∧ t.eval=p := by
  induction hp with
  | generator a => exact ⟨.leaf a,by simp [DeligneDrinfeld.UniversalEmbedding.Tree.eval]⟩
  | bracket hp hq ihp ihq =>
    obtain ⟨t,ht,rfl⟩ := ihp
    obtain ⟨u,hu,rfl⟩ := ihq
    exact ⟨.node t u,by simp [ht,hu,DeligneDrinfeld.UniversalEmbedding.Tree.eval]⟩

 theorem piece_eq (wt : α → ℕ) (n : ℕ) : weightPiece wt n=homogeneousLie (R:=ℝ) wt n := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro p hp
    exact Submodule.subset_span (word_tree hp)
  · apply Submodule.span_le.mpr
    rintro p ⟨t,ht,rfl⟩
    apply Submodule.subset_span
    exact ht ▸ tree_word wt t

 theorem embed_homogeneous {wt : α → ℕ} {n : ℕ} {p : FreeLieAlgebra ℝ α}
    (hp : p∈weightPiece wt n) : DeligneDrinfeld.AssociativeElimination.embed p∈
      DeligneDrinfeld.WordGrading.homogeneous wt n := by
  rw [piece_eq] at hp
  exact homogeneousLie_embed hp

 theorem bracket_mem {wt : α → ℕ} {n m : ℕ} {a b : FreeLieAlgebra ℝ α}
    (ha : a∈weightPiece wt n) (hb : b∈weightPiece wt m) : ⁅a,b⁆∈weightPiece wt (n+m) := by
  apply Submodule.span_induction (p:=fun a _ => ⁅a,b⁆∈weightPiece wt (n+m)) ?_ ?_ ?_ ?_ ha
  · intro a ha
    apply Submodule.span_induction (p:=fun b _ => ⁅a,b⁆∈weightPiece wt (n+m)) ?_ ?_ ?_ ?_ hb
    · intro b hb; exact Submodule.subset_span (WeightedWord.bracket ha hb)
    · rw [lie_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [lie_add]; exact Submodule.add_mem _ ha hb
    · intro s b _ hb; rw [lie_smul]; exact Submodule.smul_mem _ s hb
  · rw [zero_lie]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [add_lie]; exact Submodule.add_mem _ ha hb
  · intro s a _ ha; rw [smul_lie]; exact Submodule.smul_mem _ s ha

 theorem map_mem {β : Type*} (f : FreeLieAlgebra ℝ α →ₗ⁅ℝ⁆ FreeLieAlgebra ℝ β)
    (wa : α → ℕ) (wb : β → ℕ) (hf : ∀ a,f (FreeLieAlgebra.of ℝ a)∈weightPiece wb (wa a))
    {n : ℕ} {p : FreeLieAlgebra ℝ α} (hp : p∈weightPiece wa n) : f p∈weightPiece wb n := by
  have hw : ∀ n p,WeightedWord wa n p → f p∈weightPiece wb n := by
    intro n p hp
    induction hp with
    | generator a => exact hf a
    | bracket hp hq ihp ihq => rw [LieHom.map_lie]; exact bracket_mem ihp ihq
  apply Submodule.span_induction (p:=fun p _ => f p∈weightPiece wb n) ?_ ?_ ?_ ?_ hp
  · intro p hp; exact hw n p hp
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro p q _ _ hp hq; rw [map_add]; exact Submodule.add_mem _ hp hq
  · intro s p _ hp; rw [map_smul]; exact Submodule.smul_mem _ s hp

 theorem eval_mem {n : ℕ} {p : L} (hp : p∈Ln n) {a b : L} (ha : a∈Ln 1) (hb : b∈Ln 1) :
    eval a b p∈Ln n := by
  apply map_mem (eval a b) (fun _ => 1) (fun _ => 1) (fun i => ?_) hp
  cases i <;> simpa [eval] using (by assumption : _∈Ln 1)

 theorem x_mem : x∈Ln 1 := Submodule.subset_span (WeightedWord.generator _)
 theorem y_mem : y∈Ln 1 := Submodule.subset_span (WeightedWord.generator _)

end RealDeligneDrinfeld.WeightBridge

namespace DeligneDrinfeld.UnitConjugation
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

def hom (u : Aˣ) : A →ₐ[R] A where
  toFun a := (u:A)*a*((u⁻¹:Aˣ):A)
  map_zero' := by simp only [mul_zero,zero_mul]
  map_one' := by simp only [mul_one,Units.mul_inv]
  map_add' a b := by rw [mul_add,add_mul]
  map_mul' a b := by
    simp only [mul_assoc]
    rw [←mul_assoc (((u⁻¹:Aˣ):A)) (u:A),Units.inv_mul,one_mul]
  commutes' r := by
    rw [←Algebra.commutes,mul_assoc,Units.mul_inv,mul_one]

@[simp] theorem hom_apply (u : Aˣ) (a : A) : hom (R:=R) u a=(u:A)*a*((u⁻¹:Aˣ):A) := rfl

@[simp] theorem inverse (u : Aˣ) (a : A) : hom (R:=R) u⁻¹ (hom (R:=R) u a)=a := by
  simp only [hom_apply,inv_inv,mul_assoc]
  rw [Units.inv_mul_cancel_left,Units.inv_mul,mul_one]

@[simp] theorem mul_apply (u v : Aˣ) (a : A) : hom (R:=R) (u*v) a=hom (R:=R) u (hom (R:=R) v a) := by
  simp only [hom_apply,Units.val_mul,mul_inv_rev,mul_assoc]

theorem natural {B : Type*} [Ring B] [Algebra R B] (f : A →ₐ[R] B) (u : Aˣ) (a : A) :
    f (hom (R:=R) u a)=hom (R:=R) (Units.map f.toMonoidHom u) (f a) := by
  simp only [hom_apply,map_mul]
  rfl

end DeligneDrinfeld.UnitConjugation

namespace DeligneDrinfeld.KZCollar
open FinitePicard
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem associator_swap (F : NilpotentFiltration A) {X Y : A}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    associator F Y X=Ring.inverse (associator F X Y) := by
  unfold associator rightSolution
  norm_num only [show (1:ℝ)-1/2=1/2 by norm_num]
  rw [Ring.inverse_mul (Or.inr (normalizedSolution_isUnit F hX hY (1/2))),
    Ring.inverse_inverse (normalizedSolution_isUnit F hY hX (1/2))]

end DeligneDrinfeld.KZCollar

namespace DeligneDrinfeld.KZSwap

section
open CutoffDepth CutoffKZ KZComparison

def swap (N : ℕ) : Q ℝ N →ₐ[ℝ] Q ℝ N :=
  NilpotentFreeLift.eval (weight N) (fun b => gen N (!b)) (fun b => gen_weight N (!b))
@[simp] theorem swap_gen (N : ℕ) (b : Bool) : swap N (gen N b)=gen N (!b) :=
  NilpotentFreeLift.eval_gen _ _ _ b

theorem swap_twice (N : ℕ) (u : Q ℝ N) : swap N (swap N u)=u := by
  have hh : (swap N).comp (swap N)=AlgHom.id ℝ (Q ℝ N) := by
    apply TruncatedSubstitution.hom_ext N
    intro b
    change swap N (swap N (gen N b))=gen N b
    rw [swap_gen,swap_gen,Bool.not_not]
  exact AlgHom.congr_fun hh u

theorem positive_swap (N : ℕ) : Units.map (swap N).toMonoidHom (positive N)=(positive N)⁻¹ := by
  apply Units.ext
  change swap N (positive N:Q ℝ N)=((positive N)⁻¹:(Q ℝ N)ˣ)
  rw [positive_val,KZCollar.map_associator (swap N) (weight N) (weight N) rfl
    (gen_weight N false) (gen_weight N true),swap_gen,swap_gen]
  simp only [Bool.not_false, Bool.not_true]
  rw [KZCollar.associator_swap (weight N) (gen_weight N false) (gen_weight N true),
    ←positive_val,Ring.inverse_unit]

theorem negative_swap (N : ℕ) : Units.map (swap N).toMonoidHom (negative N)=(negative N)⁻¹ := by
  apply Units.ext
  change swap N (negative N:Q ℝ N)=((negative N)⁻¹:(Q ℝ N)ˣ)
  rw [negative_val,KZCollar.map_associator (swap N) (weight N) (weight N) rfl
    ((weight N).space 1|>.neg_mem (gen_weight N false))
    ((weight N).space 1|>.neg_mem (gen_weight N true)),map_neg,map_neg,swap_gen,swap_gen]
  simp only [Bool.not_false, Bool.not_true]
  rw [KZCollar.associator_swap (weight N)
    ((weight N).space 1|>.neg_mem (gen_weight N false))
    ((weight N).space 1|>.neg_mem (gen_weight N true)),←negative_val,Ring.inverse_unit]

open ConjugateComparison
 theorem transport_swap (N : ℕ) (P : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hdual : Units.map (swap N).toMonoidHom P=P⁻¹) (u : Q ℝ N) :
    swap N (transport N P hP u)=UnitConjugation.hom (R := ℝ) P (transport N P hP (swap N u)) := by
  have hd : swap N (P:Q ℝ N)=((P⁻¹:(Q ℝ N)ˣ):Q ℝ N) := congrArg Units.val hdual
  have hi : swap N ((P⁻¹:(Q ℝ N)ˣ):Q ℝ N)=(P:Q ℝ N) := by
    have hh := congrArg (fun v => ((v⁻¹:(Q ℝ N)ˣ):Q ℝ N)) hdual
    rw [←map_inv] at hh
    change swap N (((P⁻¹:(Q ℝ N)ˣ):Q ℝ N))=(((P⁻¹)⁻¹:(Q ℝ N)ˣ):Q ℝ N) at hh
    simpa only [inv_inv] using hh
  have he : (swap N).comp (transport N P hP).toAlgHom=
      (UnitConjugation.hom (R := ℝ) P).comp ((transport N P hP).toAlgHom.comp (swap N)) := by
    apply TruncatedSubstitution.hom_ext N
    intro b
    change swap N (transport N P hP (gen N b))=
      UnitConjugation.hom (R := ℝ) P (transport N P hP (swap N (gen N b)))
    rw [ConjugateCoalgebra.transport_cutoff_gen,swap_gen,ConjugateCoalgebra.transport_cutoff_gen]
    cases b
    · change swap N (gen N false)=(P:Q ℝ N)*
        (((P⁻¹:(Q ℝ N)ˣ):Q ℝ N)*gen N true*(P:Q ℝ N))*((P⁻¹:(Q ℝ N)ˣ):Q ℝ N)
      rw [swap_gen]
      simp only [mul_assoc,Units.mul_inv_cancel_left,Units.mul_inv,mul_one,Bool.not_false]
    · change swap N (((P⁻¹:(Q ℝ N)ˣ):Q ℝ N)*gen N true*(P:Q ℝ N))=_
      rw [map_mul,map_mul,hi,hd,swap_gen]
      rfl
  exact AlgHom.congr_fun he u

 theorem theta_swap (N : ℕ) (P V : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hV : (V:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hdP : Units.map (swap N).toMonoidHom P=P⁻¹)
    (hdV : Units.map (swap N).toMonoidHom V=V⁻¹) (u : Q ℝ N) :
    swap N (ConjugateComparison.theta N P V hP hV u)=
      UnitConjugation.hom (R := ℝ) (unitArrow N P V hP hV)
        (ConjugateComparison.theta N P V hP hV (swap N u)) := by
  obtain ⟨v,rfl⟩ := (transport N P hP).surjective u
  rw [theta_transport,transport_swap N V hV hdV,transport_swap N P hP hdP]
  rw [show ConjugateComparison.theta N P V hP hV
      (UnitConjugation.hom (R:=ℝ) P (transport N P hP (swap N v))) =
      UnitConjugation.hom (R:=ℝ) (Units.map (ConjugateComparison.theta N P V hP hV).toMonoidHom P)
      (ConjugateComparison.theta N P V hP hV (transport N P hP (swap N v))) from
      UnitConjugation.natural (ConjugateComparison.theta N P V hP hV).toAlgHom P _]
  rw [theta_transport,←UnitConjugation.mul_apply]
  have he : unitArrow N P V hP hV*Units.map (ConjugateComparison.theta N P V hP hV).toMonoidHom P=V := by
    unfold unitArrow
    group
  rw [he]

 theorem arrow_swap (N : ℕ) : Units.map (swap N).toMonoidHom (arrow N)=(arrow N)⁻¹ := by
  let P := positive N
  let V := negative N
  let U := arrow N
  let θ := KZComparison.theta N
  have hθ : Units.map (swap N).toMonoidHom (Units.map θ.toMonoidHom P)=
      U*Units.map θ.toMonoidHom (Units.map (swap N).toMonoidHom P)*U⁻¹ := by
    apply Units.ext
    exact theta_swap N P V (positive_weight N) (negative_weight N)
      (positive_swap N) (negative_swap N) (P:Q ℝ N)
  have he : Units.map (swap N).toMonoidHom U=
      V⁻¹*(U*(Units.map θ.toMonoidHom P)⁻¹*U⁻¹)⁻¹ := by
    change Units.map (swap N).toMonoidHom
      (V*(Units.map θ.toMonoidHom P)⁻¹)=_
    rw [map_mul,map_inv,negative_swap,hθ,positive_swap,map_inv]
  rw [he]
  change V⁻¹*((V*(Units.map θ.toMonoidHom P)⁻¹)*(Units.map θ.toMonoidHom P)⁻¹*
    (V*(Units.map θ.toMonoidHom P)⁻¹)⁻¹)⁻¹=(V*(Units.map θ.toMonoidHom P)⁻¹)⁻¹
  group

end

open CutoffDepth CutoffKZ KZComparison

 theorem category_swap (N : ℕ) (p q : Bool) (u : Q ℝ N) :
    swap N ((category N).S p q u)=(category N).S (!p) (!q) (swap N u) := by
  have hθ := theta_swap N (positive N) (negative N) (positive_weight N) (negative_weight N)
    (positive_swap N) (negative_swap N) u
  change swap N (theta N u)=(arrow N:Q ℝ N)*theta N (swap N u)*((arrow N)⁻¹:(Q ℝ N)ˣ) at hθ
  have hU : swap N (arrow N:Q ℝ N)=((arrow N)⁻¹:(Q ℝ N)ˣ) := congrArg Units.val (arrow_swap N)
  have hI : swap N (((arrow N)⁻¹:(Q ℝ N)ˣ):Q ℝ N)=(arrow N:Q ℝ N) := by
    have h := congrArg (fun v => ((v⁻¹:(Q ℝ N)ˣ):Q ℝ N)) (arrow_swap N)
    rw [←map_inv] at h
    change swap N (((arrow N)⁻¹:(Q ℝ N)ˣ):Q ℝ N)=_ at h
    simpa only [inv_inv] using h
  cases p <;> cases q <;>
    simp only [category,GaugeAutomorphism.data,GaugeAutomorphism.map_apply,AlgEquiv.restrictScalars_apply,frames,
      Bool.not_false,Bool.not_true,Units.val_one,inv_one,mul_one,one_mul,map_mul,
      hθ,hU,hI,mul_assoc,Units.inv_mul_cancel_left,Units.inv_mul,mul_one]

 theorem value_swap (N : ℕ) : swap N (value N)= -value N := by
  have h := OperatorLog.logarithm_natural (category N).N
    ((category N).S false true-1) ((category N).S true false-1)
    ((swap N).toLinearMap.restrictScalars ℚ) (by
      intro u
      change swap N ((category N).S false true u-u)=(category N).S true false (swap N u)-swap N u
      rw [map_sub,category_swap]
      rfl) (1:Q ℝ N)
  change swap N (value N)=LogCategory.delta (category N) true false (swap N 1) at h
  rw [map_one] at h
  have hh := LogCategory.unit_cocycle (category N) false true false
  rw [LogCategory.delta_one_loop] at hh
  exact h.trans (eq_neg_of_add_eq_zero_left hh.symm)

end DeligneDrinfeld.KZSwap

namespace DeligneDrinfeld
namespace FinitePicard

section
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem parameter_integral_derivative {f f' : ℝ → ℝ → E} (hf : Continuous f.uncurry)
    (hf' : Continuous f'.uncurry) {c d x a b : ℝ} (hx : x ∈ Ioo c d)
    (hd : ∀ s ∈ Ioo c d, ∀ t ∈ uIcc a b, HasDerivAt (fun s => f s t) (f' s t) s) :
    HasDerivAt (fun s => ∫ t in a..b, f s t) (∫ t in a..b, f' x t) x := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod (isCompact_uIcc (a:=a) (b:=b))).exists_bound_of_continuousOn
    (hf'.continuousOn : ContinuousOn f'.uncurry (Icc c d ×ˢ uIcc a b))
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=Ioo c d) (bound:=fun _ => C) (Ioo_mem_nhds hx.1 hx.2) _ _ _ _
    (intervalIntegrable_const) _).2
  · exact Eventually.of_forall (fun s => (hf.uncurry_left s).aestronglyMeasurable)
  · exact (hf.uncurry_left x).intervalIntegrable a b
  · exact (hf'.uncurry_left x).aestronglyMeasurable
  · exact ae_of_all _ (fun t ht s hs => hC (s,t) ⟨⟨hs.1.le,hs.2.le⟩,uIoc_subset_uIcc ht⟩)
  · exact ae_of_all _ (fun t ht s hs => hd s hs t (uIoc_subset_uIcc ht))

end

section
open MeasureTheory Set
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def dterm (Ω Ωs : ℝ → ℝ → A) (a : ℝ) : ℕ → ℝ → ℝ → A
  | 0 => fun _ _ => 0
  | n+1 => fun s t => ∫ u in a..t, Ωs s u * term (Ω s) a n u + Ω s u * dterm Ω Ωs a n s u

@[simp] theorem dterm_zero (Ω Ωs : ℝ → ℝ → A) (a s t : ℝ) : dterm Ω Ωs a 0 s t=0 := rfl
@[simp] theorem dterm_base (Ω Ωs : ℝ → ℝ → A) (a s : ℝ) (n : ℕ) : dterm Ω Ωs a n s a=0 := by
  cases n <;> simp [dterm]

theorem continuous_term_parameter {Ω : ℝ → ℝ → A} (hΩ : Continuous Ω.uncurry) (a : ℝ) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => term (Ω p.1) a n p.2) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact intervalIntegral.continuous_parametric_primitive_of_continuous
      (f:=fun s t => Ω s t * term (Ω s) a n t) (hΩ.mul ih)

theorem continuous_dterm {Ω Ωs : ℝ → ℝ → A} (hΩ : Continuous Ω.uncurry)
    (hΩs : Continuous Ωs.uncurry) (a : ℝ) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => dterm Ω Ωs a n p.1 p.2) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact intervalIntegral.continuous_parametric_primitive_of_continuous
      (f:=fun s t => Ωs s t * term (Ω s) a n t + Ω s t * dterm Ω Ωs a n s t)
      ((hΩs.mul (continuous_term_parameter hΩ a n)).add (hΩ.mul ih))

theorem derivative_term_parameter {Ω Ωs : ℝ → ℝ → A} (hΩ : Continuous Ω.uncurry)
    (hΩs : Continuous Ωs.uncurry) {a b c d : ℝ}
    (hd : ∀ s ∈ Ioo c d, ∀ t ∈ uIcc a b, HasDerivAt (fun s => Ω s t) (Ωs s t) s)
    (n : ℕ) : ∀ s ∈ Ioo c d, ∀ t ∈ uIcc a b,
      HasDerivAt (fun s => term (Ω s) a n t) (dterm Ω Ωs a n s t) s := by
  induction n with
  | zero => exact fun s _ t _ => hasDerivAt_const s 1
  | succ n ih =>
    intro s hs t ht
    apply parameter_integral_derivative
      (f:=fun s u => Ω s u *term (Ω s) a n u)
      (f':=fun s u => Ωs s u *term (Ω s) a n u + Ω s u * dterm Ω Ωs a n s u)
      (hΩ.mul (continuous_term_parameter hΩ a n))
      ((hΩs.mul (continuous_term_parameter hΩ a n)).add (hΩ.mul (continuous_dterm hΩ hΩs a n))) hs
    intro v hv u hu
    have hu' := uIcc_subset_uIcc_left ht hu
    exact (hd v hv u hu').mul (ih v hv u hu')

end

open MeasureTheory Set
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem dterm_flat_formula {Ω Ωs B : ℝ → ℝ → A}
    (hΩ : Continuous Ω.uncurry) (hΩs : Continuous Ωs.uncurry)
    {a b s : ℝ}
    (hB : ∀ t ∈ uIcc a b, HasDerivAt (B s) (Ωs s t) t)
    (hcomm : ∀ t ∈ uIcc a b, Commute (Ω s t) (B s t))
    (n : ℕ) : ∀ t ∈ uIcc a b,
      dterm Ω Ωs a (n+1) s t =
        B s t * term (Ω s) a n t - term (Ω s) a n t * B s a := by
  induction n with
  | zero =>
    intro t ht
    simp only [dterm,term_zero,mul_one,mul_zero,add_zero,one_mul]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => hB u (uIcc_subset_uIcc_left ht hu))
      ((hΩs.uncurry_left s).intervalIntegrable a t)
  | succ n ih =>
    intro t ht
    have hd : ∀ u ∈ uIcc a t,
        HasDerivAt (fun u => B s u*term (Ω s) a (n+1) u - term (Ω s) a (n+1) u*B s a)
          (Ωs s u * term (Ω s) a (n+1) u + Ω s u * dterm Ω Ωs a (n+1) s u) u := by
      intro u hu
      have hu' := uIcc_subset_uIcc_left ht hu
      have hp := derivative_succ (hΩ.uncurry_left s) a u n
      apply ((hB u hu').mul hp |>.sub (hp.mul_const (B s a))).congr_deriv
      rw [ih u hu']
      rw [←mul_assoc (B s u) (Ω s u),←(hcomm u hu').eq]
      noncomm_ring
    have hi := (((hΩs.uncurry_left s).mul (continuous_term (hΩ.uncurry_left s) a (n+1))).add
      ((hΩ.uncurry_left s).mul ((continuous_dterm hΩ hΩs a (n+1)).comp
        ((continuous_const : Continuous (fun _ : ℝ => s)).prodMk continuous_id)))).intervalIntegrable (μ:=volume) a t
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
    simpa only [dterm,term_base,mul_zero,zero_mul,sub_self,sub_zero] using hh

variable [FiniteDimensional ℝ A]

theorem derivative_transport_flat (F : NilpotentFiltration A) {Ω Ωs B : ℝ → ℝ → A}
    (hΩ : Continuous Ω.uncurry) (hΩs : Continuous Ωs.uncurry)
    (hΩm : ∀ s t, Ω s t ∈ F.space 1)
    {a b c d s : ℝ} (hs : s ∈ Ioo c d)
    (hDs : ∀ v ∈ Ioo c d, ∀ t ∈ uIcc a b, HasDerivAt (fun v => Ω v t) (Ωs v t) v)
    (hDt : ∀ t ∈ uIcc a b, HasDerivAt (B s) (Ωs s t) t)
    (hcomm : ∀ t ∈ uIcc a b, Commute (Ω s t) (B s t)) :
    HasDerivAt (fun s => transport (Ω s) a F.cutoff b)
      (B s b * transport (Ω s) a F.cutoff b - transport (Ω s) a F.cutoff b * B s a) s := by
  have hp (t : ℝ) : transport (Ω t) a (F.cutoff+1) b=transport (Ω t) a F.cutoff b := by
    simp only [transport,Finset.sum_range_succ,last_term_zero F (hΩm t),add_zero]
  have hd := HasDerivAt.fun_sum (u:=Finset.range (F.cutoff+2))
    (fun n _ => derivative_term_parameter hΩ hΩs hDs n s hs b right_mem_uIcc)
  have hf : (fun v => ∑ n∈Finset.range (F.cutoff+2),term (Ω v) a n b)=
      (fun v => transport (Ω v) a F.cutoff b) := by
    funext v
    exact hp v
  rw [hf] at hd
  apply hd.congr_deriv
  rw [Finset.sum_range_succ']
  simp only [dterm_zero,add_zero]
  simp_rw [dterm_flat_formula hΩ hΩs hDt hcomm _ b right_mem_uIcc]
  simp only [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.sum_mul,transport]

theorem transport_flat_constant (F : NilpotentFiltration A) {Ω Ωs B : ℝ → ℝ → A}
    (hΩ : Continuous Ω.uncurry) (hΩs : Continuous Ωs.uncurry)
    (hΩm : ∀ s t, Ω s t ∈ F.space 1)
    {a b c d u v : ℝ}
    (hDs : ∀ s ∈ Ioo c d, ∀ t ∈ uIcc a b, HasDerivAt (fun s => Ω s t) (Ωs s t) s)
    (hDt : ∀ s ∈ Ioo c d, ∀ t ∈ uIcc a b, HasDerivAt (B s) (Ωs s t) t)
    (hcomm : ∀ s ∈ Ioo c d, ∀ t ∈ uIcc a b, Commute (Ω s t) (B s t))
    (hBa : ∀ s ∈ Ioo c d, B s a=0) (hBb : ∀ s ∈ Ioo c d, B s b=0)
    (hu : u ∈ Ioo c d) (hv : v ∈ Ioo c d) :
    transport (Ω u) a F.cutoff b=transport (Ω v) a F.cutoff b := by
  have hd : ∀ s ∈ Ioo c d, HasDerivAt (fun s => transport (Ω s) a F.cutoff b) 0 s := by
    intro s hs
    simpa only [hBa s hs,hBb s hs,zero_mul,mul_zero,sub_self] using
      derivative_transport_flat F hΩ hΩs hΩm hs hDs (hDt s hs) (hcomm s hs)
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) hu hv

end FinitePicard
end DeligneDrinfeld

namespace DeligneDrinfeld.FinitePicard

section
open MeasureTheory Set Filter
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem term_congr {Ω Θ : ℝ → A} {a b : ℝ} (h : EqOn Ω Θ (uIcc a b))
    (n : ℕ) : ∀ t∈uIcc a b,term Ω a n t=term Θ a n t := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro t ht
    simp only [term_succ]
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' := uIcc_subset_uIcc_left ht hu
    change Ω u*term Ω a n u=Θ u*term Θ a n u
    rw [h hu',ih u hu']

theorem transport_congr {Ω Θ : ℝ → A} {a b : ℝ} (h : EqOn Ω Θ (uIcc a b))
    (n : ℕ) : transport Ω a n b=transport Θ a n b := by
  apply Finset.sum_congr rfl
  intro i hi
  exact term_congr h i b right_mem_uIcc

def rectExtend {a b c d : ℝ} (hab : a≤b) (hcd : c≤d) (Ω : ℝ → ℝ → A) (s t : ℝ) : A :=
  Ω (projIcc c d hcd s) (projIcc a b hab t)

omit [NormedRing A] [NormedAlgebra ℝ A] in
theorem rectExtend_eq {a b c d : ℝ} (hab : a≤b) (hcd : c≤d) (Ω : ℝ → ℝ → A)
    {s t : ℝ} (hs : s∈Icc c d) (ht : t∈Icc a b) : rectExtend hab hcd Ω s t=Ω s t := by
  simp only [rectExtend,projIcc_of_mem hcd hs,projIcc_of_mem hab ht]

omit [NormedAlgebra ℝ A] in
theorem continuous_rectExtend {a b c d : ℝ} (hab : a≤b) (hcd : c≤d) {Ω : ℝ → ℝ → A}
    (hΩ : ContinuousOn Ω.uncurry (Icc c d ×ˢ Icc a b)) : Continuous (rectExtend hab hcd Ω).uncurry := by
  apply hΩ.comp_continuous
    (((continuous_subtype_val.comp (continuous_projIcc (h:=hcd))).comp continuous_fst).prodMk
      ((continuous_subtype_val.comp (continuous_projIcc (h:=hab))).comp continuous_snd))
  intro p
  exact ⟨(projIcc c d hcd p.1).property,(projIcc a b hab p.2).property⟩

theorem rectExtend_derivative {a b c d s t : ℝ} (hab : a≤b) (hcd : c≤d)
    {Ω Ωs : ℝ → ℝ → A} (hs : s∈Ioo c d) (ht : t∈Icc a b)
    (hd : HasDerivAt (fun v => Ω v t) (Ωs s t) s) :
    HasDerivAt (fun v => rectExtend hab hcd Ω v t) (rectExtend hab hcd Ωs s t) s := by
  rw [rectExtend_eq hab hcd Ωs ⟨hs.1.le,hs.2.le⟩ ht]
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with v hv
  exact rectExtend_eq hab hcd Ω ⟨hv.1.le,hv.2.le⟩ ht

variable [CompleteSpace A] [FiniteDimensional ℝ A]

theorem derivative_transport_flat_local (F : NilpotentFiltration A) {Ω Ωs B : ℝ → ℝ → A}
    {a b c d s : ℝ} (hab : a≤b) (hcd : c≤d)
    (hΩ : ContinuousOn Ω.uncurry (Icc c d ×ˢ Icc a b))
    (hΩs : ContinuousOn Ωs.uncurry (Icc c d ×ˢ Icc a b))
    (hΩm : ∀ v∈Icc c d,∀ t∈Icc a b,Ω v t∈F.space 1)
    (hs : s∈Ioo c d)
    (hDs : ∀ v∈Ioo c d,∀ t∈Icc a b,HasDerivAt (fun v => Ω v t) (Ωs v t) v)
    (hDt : ∀ t∈Icc a b,HasDerivAt (B s) (Ωs s t) t)
    (hcomm : ∀ t∈Icc a b,Commute (Ω s t) (B s t)) :
    HasDerivAt (fun s => transport (Ω s) a F.cutoff b)
      (B s b*transport (Ω s) a F.cutoff b-transport (Ω s) a F.cutoff b*B s a) s := by
  have he (v : ℝ) (hv : v∈Icc c d) :
      transport (rectExtend hab hcd Ω v) a F.cutoff b=transport (Ω v) a F.cutoff b := by
    apply transport_congr
    intro t ht
    exact rectExtend_eq hab hcd Ω hv (by simpa only [uIcc_of_le hab] using ht)
  have hh := derivative_transport_flat F (a:=a) (b:=b) (B:=B) (continuous_rectExtend hab hcd hΩ)
    (continuous_rectExtend hab hcd hΩs)
    (fun v t => hΩm _ (projIcc c d hcd v).property _ (projIcc a b hab t).property) hs
    (fun v hv t ht => rectExtend_derivative hab hcd hv
      (by simpa only [uIcc_of_le hab] using ht) (hDs v hv t (by simpa only [uIcc_of_le hab] using ht)))
    (fun t ht => by
      rw [rectExtend_eq hab hcd Ωs ⟨hs.1.le,hs.2.le⟩ (by simpa only [uIcc_of_le hab] using ht)]
      exact hDt t (by simpa only [uIcc_of_le hab] using ht))
    (fun t ht => by
      rw [rectExtend_eq hab hcd Ω ⟨hs.1.le,hs.2.le⟩ (by simpa only [uIcc_of_le hab] using ht)]
      exact hcomm t (by simpa only [uIcc_of_le hab] using ht))
  rw [he s ⟨hs.1.le,hs.2.le⟩] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with v hv
  exact (he v ⟨hv.1.le,hv.2.le⟩).symm

end

open MeasureTheory Set Filter
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
theorem continuousOn_transport_parameter {Ω : ℝ → ℝ → A} {a b c d : ℝ}
    (hab : a≤b) (hcd : c≤d)
    (hΩ : ContinuousOn Ω.uncurry (Icc c d ×ˢ Icc a b)) (N : ℕ) :
    ContinuousOn (fun s => transport (Ω s) a N b) (Icc c d) := by
  have hh : Continuous (fun s => transport (rectExtend hab hcd Ω s) a N b) := by
    unfold transport
    apply continuous_finsetSum
    intro n hn
    exact (continuous_term_parameter (continuous_rectExtend hab hcd hΩ) a n).comp
      (continuous_id.prodMk continuous_const)
  apply hh.continuousOn.congr
  intro s hs
  apply transport_congr
  intro t ht
  exact (rectExtend_eq hab hcd Ω hs (by simpa only [uIcc_of_le hab] using ht)).symm

variable [FiniteDimensional ℝ A]

theorem transport_flat_constant_local (F : NilpotentFiltration A) {Ω Ωs B : ℝ → ℝ → A}
    {a b c d u v : ℝ} (hab : a≤b) (hcd : c<d)
    (hΩ : ContinuousOn Ω.uncurry (Icc c d ×ˢ Icc a b))
    (hΩs : ContinuousOn Ωs.uncurry (Icc c d ×ˢ Icc a b))
    (hΩm : ∀ s∈Icc c d,∀ t∈Icc a b,Ω s t∈F.space 1)
    (hDs : ∀ s∈Ioo c d,∀ t∈Icc a b,HasDerivAt (fun s => Ω s t) (Ωs s t) s)
    (hDt : ∀ s∈Ioo c d,∀ t∈Icc a b,HasDerivAt (B s) (Ωs s t) t)
    (hcomm : ∀ s∈Ioo c d,∀ t∈Icc a b,Commute (Ω s t) (B s t))
    (hBa : ∀ s∈Ioo c d,B s a=0) (hBb : ∀ s∈Ioo c d,B s b=0)
    (hu : u∈Icc c d) (hv : v∈Icc c d) :
    transport (Ω u) a F.cutoff b=transport (Ω v) a F.cutoff b := by
  have hd : ∀ s∈Ioo c d,HasDerivAt (fun s => transport (Ω s) a F.cutoff b) 0 s := by
    intro s hs
    simpa only [hBa s hs,hBb s hs,zero_mul,mul_zero,sub_self] using
      derivative_transport_flat_local F hab hcd.le hΩ hΩs hΩm hs hDs (hDt s hs) (hcomm s hs)
  let w := (c+d)/2
  have hw : w∈Ioo c d := ⟨by dsimp [w]; linarith,by dsimp [w]; linarith⟩
  have he : EqOn (fun s => transport (Ω s) a F.cutoff b)
      (fun _ => transport (Ω w) a F.cutoff b) (Ioo c d) := by
    intro s hs
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hd s hs).deriv) hs hw
  have he' := he.of_subset_closure (continuousOn_transport_parameter hab hcd.le hΩ F.cutoff)
    continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo hcd.ne])
  exact (he' hu).trans (he' hv).symm

end DeligneDrinfeld.FinitePicard

namespace DeligneDrinfeld
namespace KZFlat
variable {K : Type*} [Field K]

def wedge (u v : Fin 6 → K) (i j : Fin 6) : K :=u i*v j-u j*v i

theorem arnold (u v du dv eu ev : K) (hu : u≠0) (hv : v≠0) (huv : u+v≠0) :
    du/u*((eu+ev)/(u+v))-(du+dv)/(u+v)*(eu/u)-
      (du/u*(ev/v)-dv/v*(eu/u))+
      ((du+dv)/(u+v)*(ev/v)-dv/v*((eu+ev)/(u+v)))=0 := by
  field_simp
  ring

variable {M : Type*} [LieRing M] [LieAlgebra K M]

def combine (a b c d e f : M) (u : Fin 6 → K) : M :=
  u 0 • a+u 1 • b+u 2 • c+u 3 • d+u 4 • e+u 5 • f

theorem expand (a b c d e f : M)
    (had : ⁅a,d⁆ = -⁅a,b⁆) (hae : ⁅a,e⁆ = -⁅a,c⁆) (haf : ⁅a,f⁆=0)
    (hbd : ⁅b,d⁆ = ⁅a,b⁆) (hbe : ⁅b,e⁆=0) (hbf : ⁅b,f⁆ = -⁅b,c⁆)
    (hcd : ⁅c,d⁆=0) (hce : ⁅c,e⁆ = ⁅a,c⁆) (hcf : ⁅c,f⁆ = ⁅b,c⁆)
    (hdf : ⁅d,f⁆ = -⁅d,e⁆) (hef : ⁅e,f⁆ = ⁅d,e⁆)
    (u v : Fin 6 → K) :
    ⁅combine a b c d e f u,combine a b c d e f v⁆ =
      (wedge u v 0 1-wedge u v 0 3+wedge u v 1 3) • ⁅a,b⁆+
      (wedge u v 0 2-wedge u v 0 4+wedge u v 2 4) • ⁅a,c⁆+
      (wedge u v 1 2-wedge u v 1 5+wedge u v 2 5) • ⁅b,c⁆+
      (wedge u v 3 4-wedge u v 3 5+wedge u v 4 5) • ⁅d,e⁆ := by
  have hba : ⁅b,a⁆ = -⁅a,b⁆ := (lie_skew b a).symm
  have hca : ⁅c,a⁆ = -⁅a,c⁆ := (lie_skew c a).symm
  have hcb : ⁅c,b⁆ = -⁅b,c⁆ := (lie_skew c b).symm
  have hda : ⁅d,a⁆ = ⁅a,b⁆ := by rw [←lie_skew d a,had,neg_neg]
  have hdb : ⁅d,b⁆ = -⁅a,b⁆ := by rw [←lie_skew d b,hbd]
  have hdc : ⁅d,c⁆=0 := by rw [←lie_skew d c,hcd,neg_zero]
  have hea : ⁅e,a⁆ = ⁅a,c⁆ := by rw [←lie_skew e a,hae,neg_neg]
  have heb : ⁅e,b⁆=0 := by rw [←lie_skew e b,hbe,neg_zero]
  have hec : ⁅e,c⁆ = -⁅a,c⁆ := by rw [←lie_skew e c,hce]
  have hed : ⁅e,d⁆ = -⁅d,e⁆ := (lie_skew e d).symm
  have hfa : ⁅f,a⁆=0 := by rw [←lie_skew f a,haf,neg_zero]
  have hfb : ⁅f,b⁆ = ⁅b,c⁆ := by rw [←lie_skew f b,hbf,neg_neg]
  have hfc : ⁅f,c⁆ = -⁅b,c⁆ := by rw [←lie_skew f c,hcf]
  have hfd : ⁅f,d⁆ = ⁅d,e⁆ := by rw [←lie_skew f d,hdf,neg_neg]
  have hfe : ⁅f,e⁆ = -⁅d,e⁆ := by rw [←lie_skew f e,hef]
  simp only [combine,lie_add,add_lie,lie_smul,smul_lie,lie_self,had,hae,haf,hbd,hbe,
    hbf,hcd,hce,hcf,hdf,hef,hba,hca,hcb,hda,hdb,hdc,hea,heb,hec,hed,hfa,hfb,hfc,hfd,hfe]
  unfold wedge
  module

open GenericBraid

theorem adjacent {α : Type*} (i j k : α) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ⁅GenericBraid.t (R:=K) i j,GenericBraid.t (R:=K) j k⁆ = -⁅GenericBraid.t (R:=K) i j,GenericBraid.t (R:=K) i k⁆ := by
  have h := GenericBraid.t_three (R:=K) i j k hij hik hjk
  rw [lie_add] at h
  exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h)

theorem outer {α : Type*} (i j k : α) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ⁅GenericBraid.t (R:=K) i k,GenericBraid.t (R:=K) j k⁆ = ⁅GenericBraid.t (R:=K) i j,GenericBraid.t (R:=K) i k⁆ := by
  have h := GenericBraid.t_three (R:=K) i k j hik hij hjk.symm
  rw [GenericBraid.t_comm k j,lie_add,←lie_skew (GenericBraid.t (R:=K) i k) (GenericBraid.t (R:=K) i j)] at h
  exact (neg_add_eq_zero.mp h).symm

def dlog (z v : Fin 4 → K) (i j : Fin 4) : K :=(v i-v j)/(z i-z j)

def coefficients (z v : Fin 4 → K) : Fin 6 → K :=
  ![dlog z v 0 1,dlog z v 0 2,dlog z v 0 3,dlog z v 1 2,dlog z v 1 3,dlog z v 2 3]

def connection (z v : Fin 4 → K) : T K (Fin 4) :=
  combine (GenericBraid.t 0 1) (GenericBraid.t 0 2) (GenericBraid.t 0 3) (GenericBraid.t 1 2) (GenericBraid.t 1 3) (GenericBraid.t 2 3) (coefficients z v)

theorem arnold_dlog (z v w : Fin 4 → K) (hz : Function.Injective z)
    (i j k : Fin 4) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    dlog z v i j*dlog z w i k-dlog z v i k*dlog z w i j-
      (dlog z v i j*dlog z w j k-dlog z v j k*dlog z w i j)+
      (dlog z v i k*dlog z w j k-dlog z v j k*dlog z w i k)=0 := by
  have hu : z i-z j≠0 := sub_ne_zero.mpr (hz.ne hij)
  have hv : z j-z k≠0 := sub_ne_zero.mpr (hz.ne hjk)
  have huv : z i-z j+(z j-z k)≠0 := by simpa using sub_ne_zero.mpr (hz.ne hik)
  simpa only [dlog,sub_add_sub_cancel] using
    arnold (z i-z j) (z j-z k) (v i-v j) (v j-v k) (w i-w j) (w j-w k) hu hv huv

theorem flat (z v w : Fin 4 → K) (hz : Function.Injective z) :
    ⁅connection z v,connection z w⁆=0 := by
  rw [connection,connection,expand _ _ _ _ _ _
    (adjacent 0 1 2 (by decide) (by decide) (by decide))
    (adjacent 0 1 3 (by decide) (by decide) (by decide))
    (GenericBraid.t_disjoint 0 1 2 3 (by decide) (by decide) (by decide) (by decide))
    (outer 0 1 2 (by decide) (by decide) (by decide))
    (GenericBraid.t_disjoint 0 2 1 3 (by decide) (by decide) (by decide) (by decide))
    (adjacent 0 2 3 (by decide) (by decide) (by decide))
    (GenericBraid.t_disjoint 0 3 1 2 (by decide) (by decide) (by decide) (by decide))
    (outer 0 1 3 (by decide) (by decide) (by decide))
    (outer 0 2 3 (by decide) (by decide) (by decide))
    (adjacent 1 2 3 (by decide) (by decide) (by decide))
    (outer 1 2 3 (by decide) (by decide) (by decide))]
  dsimp [wedge,coefficients]
  rw [arnold_dlog z v w hz 0 1 2 (by decide) (by decide) (by decide),
    arnold_dlog z v w hz 0 1 3 (by decide) (by decide) (by decide),
    arnold_dlog z v w hz 0 2 3 (by decide) (by decide) (by decide),
    arnold_dlog z v w hz 1 2 3 (by decide) (by decide) (by decide)]
  simp

end KZFlat
end DeligneDrinfeld

namespace DeligneDrinfeld.LogRectangle
open MeasureTheory Set Filter FinitePicard
open scoped Topology
variable {K A E : Type*} [NontriviallyNormedField K] [NormedAlgebra ℝ K]
  [NormedRing A] [NormedAlgebra K A] [NormedAlgebra ℝ A] [IsScalarTower ℝ K A]
  [Fintype E]

def form (c : E → A) (z v : E → K) : A := ∑ i,(v i/z i) • c i

def mixed (c : E → A) (z zs zt zst : E → K) : A :=
  ∑ i,((zst i*z i-zt i*zs i)/(z i)^2) • c i

theorem derivative_s (c : E → A) {z zt : ℝ → E → K} {zs zst : E → K} {s : ℝ}
    (hz : ∀ i,HasDerivAt (fun s => z s i) (zs i) s)
    (hv : ∀ i,HasDerivAt (fun s => zt s i) (zst i) s)
    (hn : ∀ i,z s i≠0) :
    HasDerivAt (fun s => form c (z s) (zt s)) (mixed c (z s) zs (zt s) zst) s := by
  apply HasDerivAt.fun_sum
  intro i hi
  exact ((hv i).div (hz i) (hn i)).smul_const (c i)

theorem derivative_t (c : E → A) {z zs : ℝ → E → K} {zt zst : E → K} {t : ℝ}
    (hz : ∀ i,HasDerivAt (fun t => z t i) (zt i) t)
    (hv : ∀ i,HasDerivAt (fun t => zs t i) (zst i) t)
    (hn : ∀ i,z t i≠0) :
    HasDerivAt (fun t => form c (z t) (zs t)) (mixed c (z t) (zs t) zt zst) t := by
  convert derivative_s c hz hv hn using 1
  simp only [mixed,mul_comm (zt _)]

omit [NormedAlgebra ℝ K] [NormedAlgebra ℝ A] [IsScalarTower ℝ K A] in
theorem continuousOn_form (c : E → A) {X : Type*} [TopologicalSpace X]
    {z v : X → E → K} {S : Set X}
    (hz : ∀ i,ContinuousOn (fun x => z x i) S)
    (hv : ∀ i,ContinuousOn (fun x => v x i) S)
    (hn : ∀ x∈S,∀ i,z x i≠0) :
    ContinuousOn (fun x => form c (z x) (v x)) S := by
  apply continuousOn_finsetSum
  intro i hi
  exact ((hv i).div (hz i) (fun x hx => hn x hx i)).smul continuousOn_const

omit [NormedAlgebra ℝ K] [NormedAlgebra ℝ A] [IsScalarTower ℝ K A] in
theorem continuousOn_mixed (c : E → A) {X : Type*} [TopologicalSpace X]
    {z zs zt zst : X → E → K} {S : Set X}
    (hz : ∀ i,ContinuousOn (fun x => z x i) S)
    (hs : ∀ i,ContinuousOn (fun x => zs x i) S)
    (ht : ∀ i,ContinuousOn (fun x => zt x i) S)
    (hst : ∀ i,ContinuousOn (fun x => zst x i) S)
    (hn : ∀ x∈S,∀ i,z x i≠0) :
    ContinuousOn (fun x => mixed c (z x) (zs x) (zt x) (zst x)) S := by
  apply continuousOn_finsetSum
  intro i hi
  exact ((((hst i).mul (hz i)).sub ((ht i).mul (hs i))).div
    ((hz i).pow 2) (fun x hx => pow_ne_zero _ (hn x hx i))).smul continuousOn_const

variable [CompleteSpace A] [FiniteDimensional ℝ A]

theorem transport_derivative (F : NilpotentFiltration A) (c : E → A)
    {z zs zt zst : ℝ → ℝ → E → K} {a b u v s : ℝ}
    (hab : a≤b) (huv : u≤v)
    (hc : ∀ i (r : K),r • c i∈F.space 1)
    (hz : ∀ i,ContinuousOn (fun w : ℝ×ℝ => z w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hs : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zs w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (ht : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zt w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hst : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zst w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hn : ∀ s∈Icc u v,∀ t∈Icc a b,∀ i,z s t i≠0)
    (hDsz : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun s => z s t i) (zs s t i) s)
    (hDszt : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun s => zt s t i) (zst s t i) s)
    (hDtz : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun t => z s t i) (zt s t i) t)
    (hDtzs : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun t => zs s t i) (zst s t i) t)
    (hflat : ∀ t∈Icc a b,
      Commute (form c (z s t) (zt s t)) (form c (z s t) (zs s t)))
    (hss : s∈Ioo u v) :
    HasDerivAt (fun s => transport (fun t => form c (z s t) (zt s t)) a F.cutoff b)
      (form c (z s b) (zs s b)*transport (fun t => form c (z s t) (zt s t)) a F.cutoff b-
        transport (fun t => form c (z s t) (zt s t)) a F.cutoff b*form c (z s a) (zs s a)) s := by
  apply derivative_transport_flat_local F (Ω:=fun s t => form c (z s t) (zt s t)) (B:=fun s t => form c (z s t) (zs s t))
    (Ωs:=fun s t => mixed c (z s t) (zs s t) (zt s t) (zst s t)) hab huv
    (continuousOn_form c hz ht (fun w hw => hn w.1 hw.1 w.2 hw.2))
    (continuousOn_mixed c hz hs ht hst (fun w hw => hn w.1 hw.1 w.2 hw.2))
    _ hss _ _ hflat
  · intro s hs t ht
    exact (F.space 1).sum_mem (fun i hi => hc i _)
  · intro s hs t ht
    exact derivative_s c (hDsz s hs t ht) (hDszt s hs t ht) (hn s ⟨hs.1.le,hs.2.le⟩ t ht)
  · intro t ht
    exact derivative_t c (hDtz s hss t ht) (hDtzs s hss t ht) (hn s ⟨hss.1.le,hss.2.le⟩ t ht)

theorem transport_constant (F : NilpotentFiltration A) (c : E → A)
    {z zs zt zst : ℝ → ℝ → E → K} {a b u v p q : ℝ}
    (hab : a≤b) (huv : u<v)
    (hc : ∀ i (r : K),r • c i∈F.space 1)
    (hz : ∀ i,ContinuousOn (fun w : ℝ×ℝ => z w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hs : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zs w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (ht : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zt w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hst : ∀ i,ContinuousOn (fun w : ℝ×ℝ => zst w.1 w.2 i) (Icc u v ×ˢ Icc a b))
    (hn : ∀ s∈Icc u v,∀ t∈Icc a b,∀ i,z s t i≠0)
    (hDsz : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun s => z s t i) (zs s t i) s)
    (hDszt : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun s => zt s t i) (zst s t i) s)
    (hDtz : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun t => z s t i) (zt s t i) t)
    (hDtzs : ∀ s∈Ioo u v,∀ t∈Icc a b,∀ i,HasDerivAt (fun t => zs s t i) (zst s t i) t)
    (hflat : ∀ s∈Ioo u v,∀ t∈Icc a b,
      Commute (form c (z s t) (zt s t)) (form c (z s t) (zs s t)))
    (ha : ∀ s∈Ioo u v,zs s a=0) (hb : ∀ s∈Ioo u v,zs s b=0)
    (hp : p∈Icc u v) (hq : q∈Icc u v) :
    transport (fun t => form c (z p t) (zt p t)) a F.cutoff b=
      transport (fun t => form c (z q t) (zt q t)) a F.cutoff b := by
  apply transport_flat_constant_local F (Ω:=fun s t => form c (z s t) (zt s t)) (B:=fun s t => form c (z s t) (zs s t))
    (Ωs:=fun s t => mixed c (z s t) (zs s t) (zt s t) (zst s t)) hab huv
    (continuousOn_form c hz ht (fun w hw => hn w.1 hw.1 w.2 hw.2))
    (continuousOn_mixed c hz hs ht hst (fun w hw => hn w.1 hw.1 w.2 hw.2))
    _ _ _ hflat _ _ hp hq
  · intro s hs t ht
    exact (F.space 1).sum_mem (fun i hi => hc i _)
  · intro s hs t ht
    exact derivative_s c (hDsz s hs t ht) (hDszt s hs t ht) (hn s ⟨hs.1.le,hs.2.le⟩ t ht)
  · intro s hs t ht
    exact derivative_t c (hDtz s hs t ht) (hDtzs s hs t ht) (hn s ⟨hs.1.le,hs.2.le⟩ t ht)
  · intro s hs
    simp [ha s hs,form]
  · intro s hs
    simp [hb s hs,form]

end DeligneDrinfeld.LogRectangle

namespace DeligneDrinfeld.ComplexLogChamber
open MeasureTheory Set Filter FinitePicard
open scoped Topology
variable {A E : Type*} [NormedRing A] [NormedAlgebra ℂ A] [Fintype E]

def field (p : E → ℂ) (c : E → A) (z : ℂ) : A := ∑ i,(z-p i)⁻¹ • c i

def connection (p : E → ℂ) (c : E → A) (z v : ℂ) : A := v • field p c z

theorem form_eq (p : E → ℂ) (c : E → A) (z v : ℂ) :
    LogRectangle.form c (fun i => z-p i) (fun _ => v)=connection p c z v := by
  simp only [LogRectangle.form,connection,field,Finset.smul_sum,smul_smul,div_eq_mul_inv]

theorem connection_commute (p : E → ℂ) (c : E → A) (z v w : ℂ) :
    Commute (connection p c z v) (connection p c z w) := by
  change (v • field p c z)*(w • field p c z)=(w • field p c z)*(v • field p c z)
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul,mul_comm v w]

theorem connection_mem (F : NilpotentFiltration A) (p : E → ℂ) (c : E → A)
    (hc : ∀ i (r : ℂ),r • c i∈F.space 1) (z v : ℂ) : connection p c z v∈F.space 1 := by
  rw [←form_eq]
  exact (F.space 1).sum_mem (fun i hi => hc i _)

@[simp] theorem connection_zero (p : E → ℂ) (c : E → A) (z : ℂ) : connection p c z 0=0 :=
  zero_smul ℂ _

theorem connection_continuousOn (p : E → ℂ) (c : E → A)
    {X : Type*} [TopologicalSpace X] {z v : X → ℂ} {S : Set X}
    (hz : ContinuousOn z S) (hv : ContinuousOn v S)
    (hn : ∀ x∈S,∀ i,z x≠p i) : ContinuousOn (fun x => connection p c (z x) (v x)) S := by
  simp only [←form_eq]
  exact LogRectangle.continuousOn_form c (fun i => hz.sub continuousOn_const)
    (fun _ => hv) (fun x hx i => sub_ne_zero.mpr (hn x hx i))

def segment (u v : ℂ) (t : ℝ) : ℂ := (1-t) • u+t • v

@[simp] theorem segment_zero (u v : ℂ) : segment u v 0=u := by simp [segment]
@[simp] theorem segment_one (u v : ℂ) : segment u v 1=v := by simp [segment]

theorem segment_mem {C : Set ℂ} (hC : Convex ℝ C) {u v : ℂ} (hu : u∈C) (hv : v∈C)
    {t : ℝ} (ht : t∈Icc 0 1) : segment u v t∈C :=
  hC hu hv (sub_nonneg.mpr ht.2) ht.1 (by ring)

theorem segment_derivative (u v : ℂ) (t : ℝ) : HasDerivAt (segment u v) (v-u) t := by
  convert! (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).smul_const u).add
    ((hasDerivAt_id t).smul_const v) using 1
  simp [sub_eq_add_neg,add_comm]

def fundamental (F : NilpotentFiltration A) (p : E → ℂ) (c : E → A) (u v : ℂ) : A :=
  transport (fun t => connection p c (segment u v t) (v-u)) 0 F.cutoff 1

variable [CompleteSpace A] [FiniteDimensional ℝ A]

omit [CompleteSpace A] in
theorem fundamental_isUnit (F : NilpotentFiltration A) (p : E → ℂ) (c : E → A)
    (hc : ∀ i (r : ℂ),r • c i∈F.space 1) (u v : ℂ) : IsUnit (fundamental F p c u v) :=
  transport_isUnit F (fun _ => connection_mem F p c hc _ _) _ _ _

theorem fundamental_derivative (F : NilpotentFiltration A) (p : E → ℂ) (c : E → A)
    (hc : ∀ i (r : ℂ),r • c i∈F.space 1) {C : Set ℂ} {u : ℂ}
    (hp : ∀ z∈C,∀ t∈Icc (0:ℝ) 1,∀ i,segment u z t≠p i)
    {q q' : ℝ → ℂ} {a b s : ℝ} (hq : ∀ s∈Icc a b,q s∈C)
    (hqc : ContinuousOn q (Icc a b)) (hqc' : ContinuousOn q' (Icc a b))
    (hqd : ∀ s∈Ioo a b,HasDerivAt q (q' s) s) (hs : s∈Ioo a b) :
    HasDerivAt (fun s => fundamental F p c u (q s))
      (connection p c (q s) (q' s)*fundamental F p c u (q s)) s := by
  have hab : a≤b := le_trans hs.1.le hs.2.le
  have hq2 : ContinuousOn (fun w : ℝ×ℝ => q w.1) (Icc a b ×ˢ Icc 0 1) :=
    hqc.comp continuous_fst.continuousOn (fun w hw => hw.1)
  have hq2' : ContinuousOn (fun w : ℝ×ℝ => q' w.1) (Icc a b ×ˢ Icc 0 1) :=
    hqc'.comp continuous_fst.continuousOn (fun w hw => hw.1)
  have hh := LogRectangle.transport_derivative F c
    (z:=fun s t i => segment u (q s) t-p i)
    (zt:=fun s _ _ => q s-u) (zs:=fun s t _ => t • q' s) (zst:=fun s _ _ => q' s)
    (by norm_num : (0:ℝ)≤1) hab hc
    (fun i => (((continuousOn_const.sub continuous_snd.continuousOn).smul continuousOn_const).add
      (continuous_snd.continuousOn.smul hq2)).sub continuousOn_const)
    (fun _ => continuous_snd.continuousOn.smul hq2')
    (fun _ => hq2.sub continuousOn_const) (fun _ => hq2')
    (fun v hv t ht i => sub_ne_zero.mpr (hp _ (hq v hv) t ht i))
    (fun v hv t ht i => by
      simpa only [segment,Pi.add_apply,zero_add] using!
        ((hasDerivAt_const v ((1-t) • u)).add ((hqd v hv).const_smul t)).sub_const (p i))
    (fun v hv t ht i => (hqd v hv).sub_const u)
    (fun v hv t ht i => (segment_derivative u (q v) t).sub_const (p i))
    (fun v hv t ht i => by simpa only [one_smul] using! (hasDerivAt_id t).smul_const (q' v))
    (fun t ht => by rw [form_eq,form_eq]; exact connection_commute p c _ _ _) hs
  simpa only [segment_zero,segment_one,zero_smul,one_smul,form_eq,connection_zero,
    mul_zero,sub_zero,fundamental] using! hh

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
theorem fundamental_continuousOn (F : NilpotentFiltration A) (p : E → ℂ) (c : E → A)
    {C : Set ℂ} {u : ℂ}
    (hp : ∀ z∈C,∀ t∈Icc (0:ℝ) 1,∀ i,segment u z t≠p i)
    {q : ℝ → ℂ} {a b : ℝ} (hab : a≤b) (hq : ∀ s∈Icc a b,q s∈C)
    (hqc : ContinuousOn q (Icc a b)) :
    ContinuousOn (fun s => fundamental F p c u (q s)) (Icc a b) := by
  apply continuousOn_transport_parameter (a:=0) (b:=1) (by norm_num) hab _ F.cutoff
  have hq2 : ContinuousOn (fun w : ℝ×ℝ => q w.1) (Icc a b ×ˢ Icc 0 1) :=
    hqc.comp continuous_fst.continuousOn (fun w hw => hw.1)
  exact connection_continuousOn p c
    (((continuousOn_const.sub continuous_snd.continuousOn).smul continuousOn_const).add
      (continuous_snd.continuousOn.smul hq2)) (hq2.sub continuousOn_const)
    (fun w hw i => hp _ (hq w.1 hw.1) w.2 hw.2 i)

theorem transport_eq_ratio (F : NilpotentFiltration A) (p : E → ℂ) (c : E → A)
    (hc : ∀ i (r : ℂ),r • c i∈F.space 1) {C : Set ℂ} {u : ℂ}
    (hp : ∀ z∈C,∀ t∈Icc (0:ℝ) 1,∀ i,segment u z t≠p i)
    {q q' : ℝ → ℂ} {a b : ℝ} (hab : a<b) (hq : ∀ s∈Icc a b,q s∈C)
    (hqc : ContinuousOn q (Icc a b)) (hqc' : ContinuousOn q' (Icc a b))
    (hqd : ∀ s∈Ioo a b,HasDerivAt q (q' s) s) :
    transport (fun s => connection p c (q s) (q' s)) a F.cutoff b=
      fundamental F p c u (q b)*Ring.inverse (fundamental F p c u (q a)) := by
  have hcon := connection_continuousOn p c hqc hqc' (fun s hs => by simpa using hp _ (hq s hs) 1 ⟨by norm_num,le_rfl⟩)
  apply transport_eq_fundamental F (fun _ => connection_mem F p c hc _ _) hab
    (hcon.intervalIntegrable_of_Icc hab.le) (hcon.mono Ioo_subset_Icc_self)
    (fun s hs => fundamental_derivative F p c hc hp hq hqc hqc' hqd hs)
    (fundamental_continuousOn F p c hp hab.le hq hqc)
    (fun s hs => fundamental_isUnit F p c hc _ _)

end DeligneDrinfeld.ComplexLogChamber

namespace DeligneDrinfeld.KZCollar
open Set Filter FinitePicard
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem regularizedBulk_two_eq (F : NilpotentFiltration A) {X Y : A}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) {r s : ℝ}
    (hr : 0<r) (hs : 0<s) (hrs : r+s<1) :
    gauge (-Y) s*transport (bulkForm X Y) r F.cutoff (1-s)*gauge X r =
      transport (regularForm Y X) 0 F.cutoff s*associator F X Y*
        Ring.inverse (transport (regularForm X Y) 0 F.cutoff r) := by
  have hu := transport_isUnit F (regularForm_mem F hX hY) 0 r F.cutoff
  have hg : Ring.inverse (normalizedSolution F X Y r)*gauge X r =
      Ring.inverse (transport (regularForm X Y) 0 F.cutoff r) := by
    rw [Ring.inverse_mul_eq_iff_eq_mul _ _ _ (normalizedSolution_isUnit F hX hY r)]
    simp only [normalizedSolution,mul_assoc,Ring.mul_inverse_cancel _ hu,mul_one]
  have ht : 1-s∈Ioo (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  rw [bulk_transport F hX hY hr (by linarith) ht.2,left_eq_right_mul_associator F hX hY ht]
  unfold rightSolution
  rw [show 1-(1-s)=s by ring]
  simp only [normalizedSolution,mul_assoc] at hg ⊢
  rw [←mul_assoc (gauge (-Y) s) (gauge Y s),gauge_neg_mul,one_mul,hg]

theorem regularizedBulk_two_limit (F : NilpotentFiltration A) {X Y : A}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) {r s : ℝ → ℝ}
    (hr : Tendsto r (𝓝[>] 0) (𝓝[>] 0)) (hs : Tendsto s (𝓝[>] 0) (𝓝[>] 0)) :
    Tendsto (fun t => gauge (-Y) (s t)*transport (bulkForm X Y) (r t) F.cutoff (1-s t)*gauge X (r t))
      (𝓝[>] 0) (𝓝 (associator F X Y)) := by
  have h0 := (regularTransport_limit (Y:=Y) F hX).comp hr
  have h1 := (regularTransport_limit (Y:=X) F hY).comp hs
  have hi : Tendsto (fun t => Ring.inverse (transport (regularForm X Y) 0 F.cutoff (r t)))
      (𝓝[>] 0) (𝓝 (1:A)) := by
    simpa only [Units.val_one,Ring.inverse_one] using! (NormedRing.inverse_continuousAt (1:Aˣ)).tendsto.comp h0
  have hlim := (h1.mul (tendsto_const_nhds (x:=associator F X Y))).mul hi
  simp only [one_mul,mul_one] at hlim
  have hrs : ∀ᶠ t in 𝓝[>] 0,r t+s t<1 := by
    have h := (hr.mono_right nhdsWithin_le_nhds).add (hs.mono_right nhdsWithin_le_nhds)
    simpa only [zero_add] using h.eventually (eventually_lt_nhds (by norm_num))
  apply hlim.congr'
  filter_upwards [hr.eventually self_mem_nhdsWithin,hs.eventually self_mem_nhdsWithin,hrs] with t hrt hst hrst
  exact (regularizedBulk_two_eq F hX hY hrt hst hrst).symm

end DeligneDrinfeld.KZCollar

namespace DeligneDrinfeld.ComplexKZ
open Set Filter FinitePicard ComplexLogChamber
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

def form (X Y : A) (z v : ℂ) : A := (v/z) • X+(v/(z-1)) • Y

def poles : Bool → ℂ := fun b => if b then 1 else 0

def residues (X Y : A) : Bool → A := fun b => if b then Y else X

theorem form_eq (X Y : A) (z v : ℂ) :
    form X Y z v=connection poles (residues X Y) z v := by
  rw [←ComplexLogChamber.form_eq]
  simp [form,LogRectangle.form,poles,residues,add_comm]

def domain : Set ℂ := {z | 0≤z.im ∧ z≠0 ∧ z≠1}

theorem real_mem {s : ℝ} (h0 : s≠0) (h1 : s≠1) : (s:ℂ)∈domain := by
  simp [domain,h0,h1]

theorem star_avoids {z : ℂ} (hz : z∈domain) {t : ℝ} (ht : t∈Icc 0 1) (b : Bool) :
    segment Complex.I z t≠poles b := by
  intro he
  have hp : (poles b).im=0 := by cases b <;> simp [poles]
  have him := congrArg Complex.im he
  simp only [ComplexLogChamber.segment,Complex.add_im,Complex.smul_im,smul_eq_mul,Complex.I_im] at him
  rw [hp] at him
  have ht1 : t=1 := by
    have hprod : 0≤t*z.im := mul_nonneg ht.1 hz.1
    nlinarith [ht.2]
  rw [ht1,segment_one] at he
  cases b
  · exact hz.2.1 (by simpa [poles] using he)
  · exact hz.2.2 (by simpa [poles] using he)

def turn (z : ℂ) : ℂ := (1-z)⁻¹

def turnDeriv (z : ℂ) : ℂ := (1-z)⁻¹^2

theorem turn_nonzero {z : ℂ} (hz : z≠1) : turn z≠0 := by
  exact inv_ne_zero (sub_ne_zero.mpr (Ne.symm hz))

theorem turn_sub_one {z : ℂ} (hz : z≠1) : turn z-1=z/(1-z) := by
  unfold turn
  field_simp [sub_ne_zero.mpr (Ne.symm hz)]
  ring

theorem turn_ne_one {z : ℂ} (h0 : z≠0) (h1 : z≠1) : turn z≠1 := by
  intro h
  have hh := turn_sub_one h1
  rw [h,sub_self] at hh
  exact (div_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))) hh.symm

theorem turn_mem {z : ℂ} (hz : z∈domain) : turn z∈domain := by
  refine ⟨?_,turn_nonzero hz.2.2,turn_ne_one hz.2.1 hz.2.2⟩
  simp only [turn,Complex.inv_im,Complex.sub_im,Complex.one_im,zero_sub,neg_neg]
  exact div_nonneg hz.1 (Complex.normSq_nonneg _)

theorem turn_twice {z : ℂ} (h0 : z≠0) (h1 : z≠1) : turn (turn z)=(z-1)/z := by
  unfold turn
  field_simp [h0,sub_ne_zero.mpr (Ne.symm h1)]
  ring

theorem turn_thrice {z : ℂ} (h0 : z≠0) (h1 : z≠1) : turn (turn (turn z))=z := by
  rw [turn_twice h0 h1]
  unfold turn
  field_simp [h0]
  ring

theorem form_turn (X Y : A) {z : ℂ} (h0 : z≠0) (h1 : z≠1) (v : ℂ) :
    form X Y (turn z) (turnDeriv z*v)=form Y (-X-Y) z v := by
  rw [form,form,turn_sub_one h1]
  have hX : turnDeriv z*v/turn z=-(v/(z-1)) := by
    unfold turnDeriv turn
    field_simp [h0,sub_ne_zero.mpr (Ne.symm h1),sub_ne_zero.mpr h1]
    ring
  have hY : turnDeriv z*v/(z/(1-z))=v/z-v/(z-1) := by
    unfold turnDeriv
    field_simp [h0,sub_ne_zero.mpr (Ne.symm h1),sub_ne_zero.mpr h1]
    ring
  rw [hX,hY]
  simp only [sub_smul,smul_sub,smul_neg,neg_smul]
  abel

theorem turn_derivative {q : ℝ → ℂ} {q' : ℂ} {s : ℝ}
    (hq : HasDerivAt q q' s) (h1 : q s≠1) :
    HasDerivAt (fun s => turn (q s)) (turnDeriv (q s)*q') s := by
  have hd := ((hasDerivAt_const s (1:ℂ)).sub hq).inv (sub_ne_zero.mpr (Ne.symm h1))
  convert! hd using 1
  simp only [zero_sub,neg_neg,turnDeriv,Pi.sub_apply,div_eq_mul_inv,inv_pow]
  ring

theorem turn_continuousOn {q : ℝ → ℂ} {S : Set ℝ} (hq : ContinuousOn q S)
    (h1 : ∀ s∈S,q s≠1) : ContinuousOn (fun s => turn (q s)) S :=
  (continuousOn_const.sub hq).inv₀ (fun s hs => sub_ne_zero.mpr (Ne.symm (h1 s hs)))

theorem turnDeriv_continuousOn {q : ℝ → ℂ} {S : Set ℝ} (hq : ContinuousOn q S)
    (h1 : ∀ s∈S,q s≠1) : ContinuousOn (fun s => turnDeriv (q s)) S :=
  (turn_continuousOn hq h1).pow 2

theorem form_real (X Y : A) (s : ℝ) : form X Y s 1=KZCollar.bulkForm X Y s := by
  simp only [form,KZCollar.bulkForm,one_div]
  congr 1
  · rw [←Complex.ofReal_inv,Complex.coe_smul]
  · rw [←Complex.ofReal_one,←Complex.ofReal_sub,←Complex.ofReal_inv,Complex.coe_smul]

end DeligneDrinfeld.ComplexKZ

namespace DeligneDrinfeld.PowerAsymptotic
open MeasureTheory Set Filter Asymptotics FinitePicard
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

omit [NormedAlgebra ℝ A] in
theorem powerSmall_of_real_bound {f : ℝ → A} {g : ℝ → ℝ} (hg : PowerSmall g)
    (h : ∀ᶠ s in 𝓝[>] 0, ‖f s‖ ≤ g s) : PowerSmall f := by
  obtain ⟨p,hp,hg⟩ := hg
  exact ⟨p,hp,(IsBigO.of_norm_eventuallyLE h).trans hg⟩

omit [NormedAlgebra ℝ A] in
theorem subpower_of_real_bound {f : ℝ → A} {g : ℝ → ℝ} (hg : Subpower g)
    (h : ∀ᶠ s in 𝓝[>] 0, ‖f s‖ ≤ g s) : Subpower f :=
  fun p hp => (IsBigO.of_norm_eventuallyLE h).trans (hg p hp)

theorem transportPoly_subpower {L : ℝ → ℝ} (hL : Subpower L) (N : ℕ) :
    Subpower (fun s => transportPoly N (L s)) := by
  apply Subpower.sum
  intro n hn
  exact hL.pow n

theorem transport_subpower {Ω : ℝ → ℝ → A} {a b L : ℝ → ℝ}
    (h : ∀ᶠ s in 𝓝[>] 0,a s ≤ b s ∧ IntervalIntegrable (Ω s) volume (a s) (b s) ∧
      0 ≤ L s ∧ integralNorm (Ω s) (a s) (b s) ≤ L s)
    (hL : Subpower L) (N : ℕ) :
    Subpower (fun s => transport (Ω s) (a s) N (b s)) := by
  apply subpower_of_real_bound ((const_subpower ‖(1:A)‖).mul (transportPoly_subpower hL N))
  filter_upwards [h] with s hs
  exact norm_transport_le hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 N

theorem transport_perturbation_powerSmall {Ω Θ : ℝ → ℝ → A} {a b L E : ℝ → ℝ}
    (h : ∀ᶠ s in 𝓝[>] 0,a s ≤ b s ∧
      IntervalIntegrable (Ω s) volume (a s) (b s) ∧
      IntervalIntegrable (Θ s) volume (a s) (b s) ∧
      0 ≤ L s ∧ 0 ≤ E s ∧
      integralNorm (Ω s) (a s) (b s) ≤ L s ∧
      integralNorm (Θ s) (a s) (b s) ≤ L s ∧
      integralNorm (fun t => Ω s t-Θ s t) (a s) (b s) ≤ E s)
    (hL : Subpower L) (hE : PowerSmall E) (N : ℕ) :
    PowerSmall (fun s => transport (Ω s) (a s) N (b s)-transport (Θ s) (a s) N (b s)) := by
  apply powerSmall_of_real_bound
    (((const_subpower ‖(1:A)‖).mul_powerSmall hE).mul_subpower (errorPoly_subpower hL N))
  filter_upwards [h] with s hs
  exact norm_transport_sub_le hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1
    hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2 N

omit [NormedAlgebra ℝ A] in

theorem normalized_perturbation_limit {f g l r : ℝ → A}
    (h : PowerSmall (fun s => f s-g s)) (hl : Subpower l) (hr : Subpower r) :
    Tendsto (fun s => l s*f s*r s-l s*g s*r s) (𝓝[>] 0) (𝓝 0) := by
  have h' := ((hl.mul_powerSmall h).mul_subpower hr).tendsto_zero
  simpa only [mul_sub,sub_mul] using h'

end DeligneDrinfeld.PowerAsymptotic

namespace DeligneDrinfeld.ComplexKZ

section
open Set Filter MeasureTheory FinitePicard KZCollar PowerAsymptotic
open scoped Topology

def arc (r t : ℝ) : ℂ := (r:ℂ)*Complex.exp ((((1-t)*Real.pi:ℝ):ℂ)*Complex.I)

def angular : ℂ := -((Real.pi:ℂ)*Complex.I)

@[simp] theorem arc_zero (r : ℝ) : arc r 0=-(r:ℂ) := by
  simp [arc,Complex.exp_pi_mul_I]

@[simp] theorem arc_one (r : ℝ) : arc r 1=(r:ℂ) := by simp [arc]

theorem norm_arc {r : ℝ} (hr : 0≤r) (t : ℝ) : ‖arc r t‖=r := by
  simp [arc,Complex.norm_exp,hr,Real.norm_eq_abs,abs_of_nonneg]

theorem arc_mem {r t : ℝ} (hr : 0<r) (hr1 : r<1) (ht : t∈Icc 0 1) :
    arc r t∈domain := by
  have hn := norm_arc hr.le t
  refine ⟨?_,?_,?_⟩
  · simp only [arc,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
      Complex.exp_im,Complex.mul_re,Complex.I_re,mul_zero,Complex.I_im,zero_sub,neg_zero,
      Real.exp_zero,Complex.mul_im,one_mul,mul_one]
    exact mul_nonneg hr.le (Real.sin_nonneg_of_mem_Icc ⟨mul_nonneg (sub_nonneg.mpr ht.2) Real.pi_pos.le, by nlinarith [mul_nonneg ht.1 Real.pi_pos.le]⟩)
  · intro h; rw [h,norm_zero] at hn; linarith
  · intro h; rw [h,norm_one] at hn; linarith

theorem arc_derivative (r t : ℝ) : HasDerivAt (arc r) (angular*arc r t) t := by
  have hreal := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).mul_const Real.pi)
  have hcomplex := hreal.ofReal_comp
  have hexp := (Complex.hasDerivAt_exp _).scomp t (hcomplex.mul_const Complex.I)
  convert! hexp.const_mul (r:ℂ) using 1
  simp only [angular,arc,zero_sub,Complex.ofReal_neg,neg_mul,Pi.sub_apply,id_eq,smul_eq_mul]
  ring_nf

theorem arc_continuous (r : ℝ) : Continuous (arc r) :=
  continuous_iff_continuousAt.2 (fun t => (arc_derivative r t).continuousAt)

@[simp] theorem norm_angular : ‖angular‖=Real.pi := by
  simp [angular,Real.pi_pos.le,abs_of_nonneg]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

def arcForm (X Y : A) (r t : ℝ) : A := form X Y (arc r t) (angular*arc r t)

theorem arcForm_eq (X Y : A) {r : ℝ} (hr : 0<r) (t : ℝ) :
    arcForm X Y r t=angular • X+(angular*arc r t/(arc r t-1)) • Y := by
  have hn : arc r t≠0 := by intro h; have he:=norm_arc hr.le t; rw [h,norm_zero] at he; linarith
  unfold arcForm form
  rw [mul_div_cancel_right₀ _ hn]

theorem norm_arcForm_sub_le (X Y : A) {r : ℝ} (hr : 0<r) (hr1 : r≤1/2) (t : ℝ) :
    ‖arcForm X Y r t-angular • X‖≤(2*Real.pi*‖Y‖)*r := by
  rw [arcForm_eq X Y hr,add_sub_cancel_left,norm_smul,norm_div,norm_mul,norm_angular,norm_arc hr.le]
  have hden : (1:ℝ)/2≤‖arc r t-1‖ := by
    have h := norm_sub_norm_le (1:ℂ) (arc r t)
    rw [norm_one,norm_arc hr.le,norm_sub_rev] at h
    linarith
  have hb : Real.pi*r/‖arc r t-1‖≤2*Real.pi*r := by
    apply (div_le_iff₀ (by linarith : 0<‖arc r t-1‖)).mpr
    calc
      Real.pi*r=(2*Real.pi*r)*(1/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)
  exact (mul_le_mul_of_nonneg_right hb (norm_nonneg Y)).trans_eq (by ring)

theorem arcForm_continuousOn (X Y : A) {r : ℝ} (hr : 0<r) (hr1 : r<1) :
    ContinuousOn (arcForm X Y r) (Icc 0 1) := by
  change ContinuousOn (fun t => arcForm X Y r t) _
  simp only [arcForm,form_eq]
  apply ComplexLogChamber.connection_continuousOn _ _ (arc_continuous r).continuousOn
    (continuous_const.mul (arc_continuous r)).continuousOn
  intro t ht b
  cases b
  · exact (arc_mem hr hr1 ht).2.1
  · exact (arc_mem hr hr1 ht).2.2

variable [CompleteSpace A] [FiniteDimensional ℝ A]

theorem constant_transport (F : NilpotentFiltration A) {X : A} (hX : X∈F.space 1) :
    transport (fun _ => X) 0 F.cutoff 1=NormedSpace.exp X := by
  let := NormedAlgebra.restrictScalars ℚ ℝ A
  have h := transport_eq_fundamental F (fun _ => hX) (by norm_num : (0:ℝ)<1)
    intervalIntegrable_const continuousOn_const
    (f:=fun t : ℝ => NormedSpace.exp (t • X))
    (fun t ht => hasDerivAt_exp_smul_const' X t)
    (by fun_prop) (fun t ht => NormedSpace.isUnit_exp _)
  simpa using h

end

section
open Set Filter FinitePicard ComplexLogChamber
open scoped Topology

structure Path (a b : ℝ) where
  pos : a<b
  q : ℝ → ℂ
  v : ℝ → ℂ
  mem : ∀ t∈Icc a b,q t∈domain
  continuous_q : ContinuousOn q (Icc a b)
  continuous_v : ContinuousOn v (Icc a b)
  derivative : ∀ t∈Ioo a b,HasDerivAt q (v t) t

namespace Path
variable {a b : ℝ}

def rotate (P : Path a b) : Path a b where
  pos := P.pos
  q := fun t => turn (P.q t)
  v := fun t => turnDeriv (P.q t)*P.v t
  mem := fun t ht => turn_mem (P.mem t ht)
  continuous_q := turn_continuousOn P.continuous_q (fun t ht => (P.mem t ht).2.2)
  continuous_v := (turnDeriv_continuousOn P.continuous_q (fun t ht => (P.mem t ht).2.2)).mul P.continuous_v
  derivative := fun t ht => turn_derivative (P.derivative t ht) (P.mem t (Ioo_subset_Icc_self ht)).2.2

def interval (ha : 0<a) (hab : a<b) (hb : b<1) : Path a b where
  pos := hab
  q t := t
  v _ := 1
  mem t ht := real_mem (ne_of_gt (ha.trans_le ht.1)) (ne_of_lt (ht.2.trans_lt hb))
  continuous_q := Complex.continuous_ofReal.continuousOn
  continuous_v := continuousOn_const
  derivative t _ := by simpa only [Complex.ofReal_one] using! (hasDerivAt_id t).ofReal_comp

def semicircle {r : ℝ} (hr : 0<r) (hr1 : r<1) : Path 0 1 where
  pos := by norm_num
  q := arc r
  v t := angular*arc r t
  mem t ht := arc_mem hr hr1 ht
  continuous_q := (arc_continuous r).continuousOn
  continuous_v := (continuous_const.mul (arc_continuous r)).continuousOn
  derivative t _ := arc_derivative r t

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

def holonomy (F : NilpotentFiltration A) (X Y : A) (P : Path a b) : A :=
  transport (fun s => form X Y (P.q s) (P.v s)) a F.cutoff b

theorem rotate_holonomy (F : NilpotentFiltration A) (X Y : A) (P : Path a b) :
    holonomy F X Y P.rotate=holonomy F Y (-X-Y) P := by
  apply transport_congr
  intro s hs
  rw [uIcc_of_le P.pos.le] at hs
  exact form_turn X Y (P.mem s hs).2.1 (P.mem s hs).2.2 _

theorem rotate_twice_holonomy (F : NilpotentFiltration A) (X Y : A) (P : Path a b) :
    holonomy F X Y P.rotate.rotate=holonomy F (-X-Y) X P := by
  rw [rotate_holonomy,rotate_holonomy]
  congr 1
  abel

theorem interval_holonomy (F : NilpotentFiltration A) (X Y : A)
    (ha : 0<a) (hab : a<b) (hb : b<1) :
    holonomy F X Y (interval ha hab hb)=transport (KZCollar.bulkForm X Y) a F.cutoff b := by
  change transport (fun t => form X Y (t:ℂ) 1) a F.cutoff b=_
  congr 1
  funext t
  exact form_real X Y t

variable [CompleteSpace A] [FiniteDimensional ℝ A]

def frame (F : NilpotentFiltration A) (X Y : A) (z : ℂ) : A :=
  fundamental F poles (residues X Y) Complex.I z

omit [CompleteSpace A] in
theorem frame_isUnit (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) (hY : ∀ c : ℂ,c • Y∈F.space 1) (z : ℂ) :
    IsUnit (frame F X Y z) := by
  apply fundamental_isUnit
  intro b c
  cases b
  · exact hX c
  · exact hY c

theorem holonomy_ratio (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) (hY : ∀ c : ℂ,c • Y∈F.space 1) (P : Path a b) :
    holonomy F X Y P=frame F X Y (P.q b)*Ring.inverse (frame F X Y (P.q a)) := by
  unfold holonomy frame
  simp only [form_eq]
  exact transport_eq_ratio F poles (residues X Y)
    (fun b c => by cases b; exact hX c; exact hY c)
    (fun z hz t ht b => star_avoids hz ht b) P.pos P.mem P.continuous_q P.continuous_v P.derivative

end Path
end

open Set Filter FinitePicard
open scoped Topology
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem cycle_identity (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) (hY : ∀ c : ℂ,c • Y∈F.space 1)
    {a b c d : ℝ} (P : Path a b) (Q : Path c d)
    (hstart : P.q a=Q.q d) (hend : P.q b=turn (Q.q c)) :
    Path.holonomy F X Y Q*Path.holonomy F X Y P.rotate.rotate*
      Path.holonomy F X Y Q.rotate.rotate*Path.holonomy F X Y P.rotate*
      Path.holonomy F X Y Q.rotate*Path.holonomy F X Y P=1 := by
  rw [Path.holonomy_ratio F hX hY Q,Path.holonomy_ratio F hX hY P.rotate.rotate,
    Path.holonomy_ratio F hX hY Q.rotate.rotate,Path.holonomy_ratio F hX hY P.rotate,
    Path.holonomy_ratio F hX hY Q.rotate,Path.holonomy_ratio F hX hY P]
  simp only [Path.rotate]
  rw [hstart,hend,turn_thrice (Q.mem c (left_mem_Icc.mpr Q.pos.le)).2.1
    (Q.mem c (left_mem_Icc.mpr Q.pos.le)).2.2]
  have hu := Path.frame_isUnit F hX hY
  have cancel (u : ℂ) (v : A) : Ring.inverse (Path.frame F X Y u)*(Path.frame F X Y u*v)=v :=
    Ring.inverse_mul_cancel_left _ _ (hu u)
  simp only [mul_assoc,cancel,Ring.mul_inverse_cancel _ (hu _)]

def bulkEndpoint (r : ℝ) : ℝ := (1+r)⁻¹

theorem bulkEndpoint_bounds {r : ℝ} (hr : 0<r) (hr1 : r<1/2) :
    0<bulkEndpoint r ∧ r<bulkEndpoint r ∧ bulkEndpoint r<1 := by
  have hd : 0<1+r := by linarith
  refine ⟨inv_pos.mpr hd,?_,?_⟩
  · change r<(1+r)⁻¹
    rw [←one_div]
    apply (lt_div_iff₀ hd).mpr
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hr1.le)]
  · exact (inv_lt_one₀ hd).mpr (by linarith)

theorem bulkEndpoint_turn (r : ℝ) : (bulkEndpoint r:ℂ)=turn (-(r:ℂ)) := by
  simp [bulkEndpoint,turn,sub_neg_eq_add]

theorem bulk_arc_identity (F : NilpotentFiltration A) {X Y : A}
    (hX : ∀ c : ℂ,c • X∈F.space 1) (hY : ∀ c : ℂ,c • Y∈F.space 1)
    {r : ℝ} (hr : 0<r) (hr1 : r<1/2) :
    transport (arcForm X Y r) 0 F.cutoff 1*
      transport (KZCollar.bulkForm (-X-Y) X) r F.cutoff (bulkEndpoint r)*
      transport (arcForm (-X-Y) X r) 0 F.cutoff 1*
      transport (KZCollar.bulkForm Y (-X-Y)) r F.cutoff (bulkEndpoint r)*
      transport (arcForm Y (-X-Y) r) 0 F.cutoff 1*
      transport (KZCollar.bulkForm X Y) r F.cutoff (bulkEndpoint r)=1 := by
  have hb := bulkEndpoint_bounds hr hr1
  let P := Path.interval hr hb.2.1 hb.2.2
  let Q := Path.semicircle hr (by linarith : r<1)
  have hh := cycle_identity F hX hY P Q (by simp [P,Q,Path.interval,Path.semicircle])
    (by simpa [P,Q,Path.interval,Path.semicircle] using bulkEndpoint_turn r)
  rw [Path.rotate_twice_holonomy,Path.rotate_twice_holonomy,
    Path.rotate_holonomy,Path.rotate_holonomy] at hh
  dsimp only [P] at hh
  rw [Path.interval_holonomy,Path.interval_holonomy,Path.interval_holonomy] at hh
  exact hh

end DeligneDrinfeld.ComplexKZ

end

end OAI
