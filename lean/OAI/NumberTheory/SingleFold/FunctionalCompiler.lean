import OAI.NumberTheory.SingleFold.EllipticCoordinates

namespace OAI

namespace SingleFold.Compiler

def MapSF {α β : Type} (f : (α → ℕ) → (β → ℕ)) : Prop :=
  SF (fun z : α ⊕ β → ℕ => z ∘ Sum.inr=f (z ∘ Sum.inl))
namespace MapSF
variable {α β γ δ : Type}
lemma congr {f g : (α → ℕ) → (β → ℕ)} (hf : MapSF f) (hfg : ∀ z, f z=g z) : MapSF g :=
  SF.congr hf (by intro z; rw [hfg])
lemma proj (i : β → α) [Finite β] : MapSF (fun z => z ∘ i) := by
  have h := SF.all (fun j : β => SF.eq (Poly.proj (Sum.inr j : α⊕β)) (Poly.proj (Sum.inl (i j))))
  refine h.congr ?_
  intro z
  change (∀ j, (z (Sum.inr j):ℤ)=z (Sum.inl (i j))) ↔ _
  simp only [Int.natCast_inj]
  exact ⟨fun h => funext h,fun h j => congrFun h j⟩
lemma const (b : β → ℕ) [Finite β] : MapSF (fun _ : α → ℕ => b) := by
  have h := SF.all (fun j : β => SF.eq (Poly.proj (Sum.inr j : α⊕β)) (Poly.const (b j)))
  refine h.congr ?_
  intro z
  change (∀ j, (z (Sum.inr j):ℤ)=(b j:ℤ)) ↔ _
  simp only [Int.natCast_inj]
  exact ⟨fun h => funext h,fun h j => congrFun h j⟩
lemma reindex {f : (α → ℕ) → (β → ℕ)} (hf : MapSF f) (i : α → γ) :
    MapSF (fun z => f (z ∘ i)) := by
  exact (SF.reindex hf (Sum.map i id)).congr (by intro z; rfl)
lemma comp {f : (α → ℕ) → (β → ℕ)} {g : (β → ℕ) → (γ → ℕ)} [Finite β]
    (hg : MapSF g) (hf : MapSF f) : MapSF (fun z => g (f z)) := by
  have h := (SF.reindex hf (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr)).and
    (SF.reindex hg (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)))
  have hu : ∀ (z : α⊕γ → ℕ) (x y : β → ℕ),
      (x=f (z ∘ Sum.inl) ∧ z ∘ Sum.inr=g x) →
      (y=f (z ∘ Sum.inl) ∧ z ∘ Sum.inr=g y) → x=y := by
    intro z x y hx hy; exact hx.1.trans hy.1.symm
  refine (h.ex hu).congr ?_
  intro z
  change (∃ x, x=f (z ∘ Sum.inl) ∧ z ∘ Sum.inr=g x) ↔ _
  simp only [exists_eq_left]
lemma pair {f : (α → ℕ) → (β → ℕ)} {g : (α → ℕ) → (γ → ℕ)}
    (hf : MapSF f) (hg : MapSF g) : MapSF (fun z => Sum.elim (f z) (g z)) := by
  have h := (SF.reindex hf (Sum.map id Sum.inl)).and (SF.reindex hg (Sum.map id Sum.inr))
  refine h.congr ?_
  intro z
  change (z ∘ Sum.inr ∘ Sum.inl=f (z ∘ Sum.inl) ∧ z ∘ Sum.inr ∘ Sum.inr=g (z ∘ Sum.inl)) ↔ _
  constructor
  · rintro ⟨h₁,h₂⟩; funext j; cases j with
    | inl j => exact congrFun h₁ j
    | inr j => exact congrFun h₂ j
  · intro h
    exact ⟨congrArg (fun z => z ∘ Sum.inl) h,congrArg (fun z => z ∘ Sum.inr) h⟩
lemma all [Finite δ] {f : δ → (α → ℕ) → (β → ℕ)} (hf : ∀ d, MapSF (f d)) :
    MapSF (fun z (v : δ×β) => f v.1 z v.2) := by
  have h := SF.all (fun d => SF.reindex (hf d) (Sum.map id (fun j => (d,j))))
  refine h.congr ?_
  intro z
  constructor
  · intro hh; funext ⟨d,j⟩; exact congrFun (hh d) j
  · intro hh d; funext j; exact congrFun hh (d,j)
lemma pullback {f : (α → ℕ) → (β → ℕ)} [Finite β] (hf : MapSF f)
    {R : (β → ℕ) → Prop} (hR : SF R) : SF (fun z => R (f z)) := by
  have h := hf.and (hR.reindex Sum.inr)
  refine (h.ex (fun z x y hx hy => hx.1.trans hy.1.symm)).congr ?_
  intro z
  change (∃ x, x=f z ∧ R x) ↔ _
  simp only [exists_eq_left]
end MapSF
end SingleFold.Compiler

namespace SingleFold.PointCompiler
open Compiler RationalCompiler
noncomputable def Code.decode (a : Code) : E.Point := by
  classical
  exact if h : a.Valid then a.toPoint h else 0
lemma decode_encode (P : E.Point) : (encode P).decode=P := by
  rw [Code.decode,dite_eq_left (encode_valid P),encode_toPoint]
lemma normalized_graph : MapSF (fun z : Var → ℕ => tuple (encode (fromTuple z).decode)) := by
  let v := code_valid_semi.reindex (Sum.inl : Var → Var⊕Var)
  have ht : SF (fun z : Var⊕Var → ℕ => z ∘ Sum.inr=z ∘ Sum.inl) := MapSF.proj id
  have hz : SF (fun z : Var⊕Var → ℕ => z ∘ Sum.inr=tuple (encode 0)) := MapSF.const _
  have h := (v.1.and ht).or (v.2.and hz) (by intro z; tauto)
  refine h.congr ?_
  intro z
  change (((fromTuple (z ∘ Sum.inl)).Valid ∧ z ∘ Sum.inr=z ∘ Sum.inl) ∨
    ¬(fromTuple (z ∘ Sum.inl)).Valid ∧ z ∘ Sum.inr=tuple (encode 0)) ↔ _
  by_cases hv : (fromTuple (z ∘ Sum.inl)).Valid
  · simp only [hv,true_and,not_true,false_and,or_false]
    rw [Code.decode,dite_eq_left hv,Code.encode_toPoint,tuple_from]
  · simp only [hv,false_and,not_false_eq_true,true_and,false_or]
    rw [Code.decode,dite_eq_right hv]

def PointSF {α : Type} (f : (α → ℕ) → E.Point) : Prop := MapSF (fun z => tuple (encode (f z)))
namespace PointSF
variable {α β : Type} {f g : (α → ℕ) → E.Point}
lemma const (P : E.Point) : PointSF (fun _ : α → ℕ => P) := MapSF.const _
lemma var (i : Var → α) : PointSF (fun z => (fromTuple (z ∘ i)).decode) :=
  MapSF.reindex normalized_graph i
lemma reindex (hf : PointSF f) (i : α → β) : PointSF (fun z => f (z ∘ i)) :=
  MapSF.reindex hf i
lemma add (hf : PointSF f) (hg : PointSF g) : PointSF (fun z => f z+g z) := by
  have hf' := MapSF.reindex hf (Sum.inl : α → α⊕Var)
  have hg' := MapSF.reindex hg (Sum.inl : α → α⊕Var)
  have hframe := MapSF.pair (MapSF.pair hf' hg') (MapSF.proj (Sum.inr : Var → α⊕Var))
  have h := hframe.pullback (add_general_sf (Sum.inl ∘ Sum.inl) (Sum.inl ∘ Sum.inr) Sum.inr)
  refine h.congr ?_
  intro z
  simp only [Function.comp_def,Sum.elim_inl,Sum.elim_inr,from_tuple] at h ⊢
  change ((encode (f (z ∘ Sum.inl))).Valid ∧ (encode (g (z ∘ Sum.inl))).Valid ∧
    (fromTuple (z ∘ Sum.inr)).Valid ∧ AddEq (encode (f (z ∘ Sum.inl))) (encode (g (z ∘ Sum.inl)))
      (fromTuple (z ∘ Sum.inr))) ↔ _
  constructor
  · rintro ⟨_,_,hv,he⟩
    have hh := (addEq_spec _ _ _ (encode_valid _) (encode_valid _) hv).mp he
    rw [encode_toPoint,encode_toPoint] at hh
    have hc : fromTuple (z ∘ Sum.inr)=encode (f (z ∘ Sum.inl)+g (z ∘ Sum.inl)) := by
      rw [hh,Code.encode_toPoint]
    exact fromTuple_injective (hc.trans (from_tuple _).symm)
  · intro he
    have hc := congrArg fromTuple he
    rw [from_tuple] at hc
    change fromTuple (z ∘ Sum.inr)=encode (f (z ∘ Sum.inl)+g (z ∘ Sum.inl)) at hc
    rw [hc]
    exact ⟨encode_valid _,encode_valid _,encode_valid _,(addEq_encode _ _ _).mpr rfl⟩
lemma smul (n : ℕ) (hf : PointSF f) : PointSF (fun z => n • f z) := by
  have hframe := MapSF.pair (MapSF.reindex hf (Sum.inl : α → α⊕Var))
    (MapSF.proj (Sum.inr : Var → α⊕Var))
  refine (hframe.pullback (mulRel_sf n Sum.inl Sum.inr)).congr ?_
  intro z
  change MulRel n (fromTuple (tuple (encode (f (z ∘ Sum.inl))))) (fromTuple (z ∘ Sum.inr)) ↔ _
  rw [from_tuple]
  constructor
  · rintro ⟨P,hP,hout⟩
    have hp := encode_injective hP
    subst P
    exact fromTuple_injective (hout.trans (from_tuple _).symm)
  · intro he
    refine ⟨f (z ∘ Sum.inl),rfl,?_⟩
    have hh := congrArg fromTuple he
    simpa only [from_tuple] using hh
lemma height (m : ℕ) (hf : PointSF f) :
    MapSF (fun z (_ : Unit) => (encode (m • f z)).height) := by
  have hframe := MapSF.pair (MapSF.reindex hf (Sum.inl : α → α⊕Unit))
    (MapSF.proj (Sum.inr : Unit → α⊕Unit))
  refine (hframe.pullback (wRel_sf m Sum.inl (Sum.inr ()))).congr ?_
  intro z
  change WRel m (fromTuple (tuple (encode (f (z ∘ Sum.inl))))) (z (Sum.inr ())) ↔ _
  rw [from_tuple,wRel_semantics]
  constructor
  · rintro ⟨P,hP,hv⟩
    have hp := encode_injective hP
    subst P
    funext j; cases j; exact hv.symm
  · intro he
    exact ⟨f (z ∘ Sum.inl),rfl,(congrFun he ()).symm⟩
end PointSF
end SingleFold.PointCompiler

namespace SingleFold.Compiler
def ScalarSF {α : Type} (f : (α → ℕ) → ℕ) : Prop := MapSF (fun z (_ : Unit) => f z)
namespace ScalarSF
variable {α : Type} {f g : (α → ℕ) → ℕ}
lemma const (n : ℕ) : ScalarSF (fun _ : α → ℕ => n) := MapSF.const _
lemma proj (i : α) : ScalarSF (fun z => z i) := MapSF.proj (fun _ => i)
lemma poly {f : (α → ℕ) → ℕ} (p : Poly α) (hp : ∀ z, p z=(f z:ℤ)) : ScalarSF f := by
  have h := SF.eq (Poly.proj (Sum.inr () : α⊕Unit)) (p.map Sum.inl)
  refine h.congr ?_
  intro z
  change (z (Sum.inr ()):ℤ)=p (z ∘ Sum.inl) ↔ _
  rw [hp,Int.natCast_inj]
  exact ⟨fun hh => funext (fun j => by cases j; exact hh),fun hh => congrFun hh ()⟩
lemma add (hf : ScalarSF f) (hg : ScalarSF g) : ScalarSF (fun z => f z+g z) := by
  have h : ScalarSF (fun z : Unit⊕Unit → ℕ => z (.inl ())+z (.inr ())) :=
    poly (Poly.proj (.inl ())+Poly.proj (.inr ())) (by intro z; simp)
  exact MapSF.comp h (MapSF.pair hf hg)
lemma mul (hf : ScalarSF f) (hg : ScalarSF g) : ScalarSF (fun z => f z*g z) := by
  have h : ScalarSF (fun z : Unit⊕Unit → ℕ => z (.inl ())*z (.inr ())) :=
    poly (Poly.proj (.inl ())*Poly.proj (.inr ())) (by intro z; simp)
  exact MapSF.comp h (MapSF.pair hf hg)
lemma pow (hf : ScalarSF f) (n : ℕ) : ScalarSF (fun z => f z^n) := by
  have h : ScalarSF (fun z : Unit → ℕ => z ()^n) :=
    poly (Poly.proj ()^n) (by
      intro z
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ,Poly.mul_apply,ih,Poly.proj_apply,Nat.cast_pow,←pow_succ,Nat.cast_pow])
  exact MapSF.comp h hf
lemma max (hf : ScalarSF f) (hg : ScalarSF g) : ScalarSF (fun z => max (f z) (g z)) := by
  have h : ScalarSF (fun z : Unit⊕Unit → ℕ => Max.max (z (.inl ())) (z (.inr ()))) := by
    refine (Semi.max_eq (Poly.proj (.inl (.inl ()))) (Poly.proj (.inl (.inr ())))
      (Poly.proj (.inr ()))).1.congr ?_
    intro z
    change Max.max (z (.inl (.inl ())):ℤ) (z (.inl (.inr ())) : ℤ)=(z (.inr ()):ℤ) ↔ _
    rw [←Nat.cast_max,Int.natCast_inj]
    exact ⟨fun hh => funext (fun j => by cases j; exact hh.symm),fun hh => (congrFun hh ()).symm⟩
  exact MapSF.comp h (MapSF.pair hf hg)
lemma le (hf : ScalarSF f) (hg : ScalarSF g) : SF (fun z => f z≤g z) := by
  have h := (MapSF.pair hf hg).pullback (SF.le (Poly.proj (.inl ())) (Poly.proj (.inr ())))
  refine h.congr ?_
  intro z
  change (f z:ℤ)≤(g z:ℤ) ↔ _
  exact_mod_cast Iff.rfl
lemma lt (hf : ScalarSF f) (hg : ScalarSF g) : SF (fun z => f z<g z) := by
  have h := (MapSF.pair hf hg).pullback (SF.lt (Poly.proj (.inl ())) (Poly.proj (.inr ())))
  refine h.congr ?_
  intro z
  change (f z:ℤ)<(g z:ℤ) ↔ _
  exact_mod_cast Iff.rfl
lemma eq (hf : ScalarSF f) (hg : ScalarSF g) : SF (fun z => f z=g z) := by
  have h := (MapSF.pair hf hg).pullback (SF.eq (Poly.proj (.inl ())) (Poly.proj (.inr ())))
  refine h.congr ?_
  intro z
  change (f z:ℤ)=(g z:ℤ) ↔ _
  exact_mod_cast Iff.rfl
end ScalarSF
end SingleFold.Compiler

namespace SingleFold.PointCompiler
open Compiler RationalCompiler
lemma exprLe_semi {ι : Type} [Finite ι] (p q : Expr (ι×Fin 2)) :
    Semi (fun z => AllValid z ∧ p.eval (values z)≤q.eval (values z)) :=
  Expr.le_under allValid_semi ratMap allValid_rational p q
namespace PointSF
variable {α : Type} {f g : (α → ℕ) → E.Point}
lemma nonzero (hf : PointSF f) : SF (fun z => f z≠0) := by
  have h := hf.pullback ((Semi.eq (Poly.proj (Sum.inl () : Var)) 0).1)
  refine h.congr ?_
  intro z
  change ((encode (f z)).flag:ℤ)=0 ↔ _
  cases f z <;> simp [encode,←WeierstrassCurve.Affine.Point.zero_def]
lemma xle (hf : PointSF f) (hg : PointSF g) :
    SF (fun z => (encode (f z)).x.value≤(encode (g z)).x.value) := by
  have hh := MapSF.all (f:=fun i : Fin 2 => if i=0 then (fun z => tuple (encode (f z))) else (fun z => tuple (encode (g z))))
    (fun i => by fin_cases i; exact hf; exact hg)
  have he := (exprLe_semi (xe (0:Fin 2)) (xe 1)).1
  refine (hh.pullback he).congr ?_
  intro z
  let frame : Fin 2×Var → ℕ := fun v => (if v.1=0 then (fun z => tuple (encode (f z))) else (fun z => tuple (encode (g z)))) z v.2
  change (AllValid frame ∧ (At frame 0).x.value≤(At frame 1).x.value) ↔ _
  have h₀ : At frame 0=encode (f z) := from_tuple _
  have h₁ : At frame 1=encode (g z) := from_tuple _
  have hv : AllValid frame := by
    intro i; fin_cases i
    · change (At frame 0).Valid
      rw [h₀]; exact encode_valid _
    · change (At frame 1).Valid
      rw [h₁]; exact encode_valid _
  rw [h₀,h₁]
  simp only [hv,true_and]
lemma ynonneg (hf : PointSF f) : SF (fun z => 0≤(encode (f z)).y.value) := by
  have hh := MapSF.all (fun _ : Unit => hf)
  refine (hh.pullback (exprLe_semi (ι:=Unit) 0 (ye ()) ).1).congr ?_
  intro z
  change (AllValid (fun v : Unit×Var => tuple (encode (f z)) v.2) ∧ 0≤(encode (f z)).y.value) ↔ _
  have hv : AllValid (fun v : Unit×Var => tuple (encode (f z)) v.2) := by
    intro i; exact (by simpa only [At,from_tuple] using encode_valid (f z))
  simp only [hv,true_and]
end PointSF
end SingleFold.PointCompiler

end OAI
