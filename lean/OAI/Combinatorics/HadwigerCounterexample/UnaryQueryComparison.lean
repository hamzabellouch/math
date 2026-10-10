import OAI.Combinatorics.HadwigerCounterexample.BinaryMixingBounds

namespace OAI

/-! # Unary Query Comparison -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset Filter Function LinearMap
variable {p : Shape} {n N : ℕ}

namespace Template

def solo (p : Shape) (t : Tag p.g) (s : Label p.b) (f : Flavor p.g) :
    Template p Unit := ⟨fun _ => true,fun _=>t,fun _ =>s,fun _=>f⟩

abbrev Solo (p : Shape) := Template p Unit
variable (v : Solo p)

def soloeq (N : ℕ) : Keys (p:=p) v.t N ≃ AtomKey (p:=p) (v.t ()) N where
  toFun x := x ()
  invFun x i := i.rec x
  left_inv x := by funext i; cases i; rfl
  right_inv x := rfl

theorem soloprice (q : F) :
    mapW (lawNu p N v.t (fun _ => q)) (soloeq v N)=lawOmega p N (v.t ()) q := by
  have hh : ownPart (p:=p) v.t (fun _=>q) = fun x => ownOne p _ q (soloeq v N x) := by
    funext x
    apply propext
    rw [ownPart_def]
    constructor
    · intro h; exact h.1 ()
    intro h; exact ⟨fun i => (by cases i; exact h),fun i j _ _ _ hi => (hi
      (Subsingleton.elim i j)).elim⟩
  unfold lawNu; rw [hh]; exact on_equiv ..

set_option maxHeartbeats 800000 in
theorem solo_data (x : Knobs p.g n) (m : Mixer p n) (q : F)
    (hj : 1≤p.j) (h : dialed p (v.t ()) (v.f ()) x=q) :
    let k := ownPort (p:=p) v.t
    let A := queryLaw v (fun _ => x) (g:=k)
    (∀ i,Injective (A i).mulVec)∧ database m A A = ownMap v.t (fun _=>q) := by
  classical
  intro k A
  have ht i : Subsingleton (Port k i) := ⟨fun p q => (own_inj v i)
    (Subsingleton.elim _ _)⟩
  let s := v.s (); let l:=v.t (); let f := v.f (); let z := lit f l x
  let u := point p s z
  have he i (j : Port k i) :
      (A i).col j=u := by
    unfold A queryLaw u s z f l; rcases j with ⟨⟨a,w⟩,h⟩; cases a; rfl
  constructor
  · intro i x y h
    have := ht i
    funext j
    let t : Row p n := (emptySel,none)
    have hf : A i t j=1 := congr_fun (he i j) t |>.trans (point_base_eval p s z none)
    have hh (x) : ((A i) *ᵥ x) t=x j := by
      change ∑ j,A i t j*x j=_
      rw [Finset.sum_eq_single j]
      · rw [hf,one_mul]
      · intro k _ h; exact (h (Subsingleton.elim _ _)).elim
      simp
    rw [←hh x,←hh y]; exact congr_fun h _
  funext i
  ext j t
  have h1 := ht i |>.elim j t; subst t
  unfold database ownMap
  rw [diagonal_apply_eq]
  let E := selfM p n m.mixM
  have heM : mpair E (mom p s z)=q := (selfM_pair p hj _ (Submodule.subset_span
    ⟨_,_,rfl⟩)).trans ((etaScan p l s f x).symm.trans h)
  change (pullM (A i) (A i) E) j j=q

  have hh : (pullM (A i) (A i) E) j j=evmat E ((A i).col j) ((A i).col j) := by
    rw [pullM_def,Matrix.mul_assoc]; rfl
  rw [hh,he,← mpair_outer]
  exact heM

def desc (v : Solo p) (x : Knobs p.g n) (o : Orient p n N) := callOne v () x o
set_option maxHeartbeats 800000 in
theorem solo_read (v : Solo p) (m : Mixer p n) (hN : 2*num (Full p n)<N)
    (x : Knobs p.g n) (q : F) (hj : 1 ≤ p.j)
    (h : dialed p (v.t ()) (v.f ()) x=q)
    (f : Wgt (AtomKey (p:=p) (v.t ()) N)) (hf : ∀ i,|f i|≤1)
    (k : ℝ) (hk : ∀ i,num (Port (ownPort (p:=p) v.t) i) ≤ k) (hK : 2*k-N≤ -1) :
    |avg (raw m N) (f ∘ (v.desc x))-avg (lawOmega p N (v.t ()) q) f| ≤
      2 * netFact (ownPort (p:=p) v.t) * (num (Comp p.g)*(2*bp (k-N))) := by
  classical
  let g := ownPort (p:=p) v.t
  let z := fun (_ : Unit) => x
  let A := v.queryLaw z (g:=g)
  let T := (v.singleP n).showKey (N:=N) z
  let W := scatter v.t N; let Q := soloeq v N
  let u := fun x => f (Q (W.symm x))
  have ht (i) : u (T i)=f (v.desc x i) := by
    unfold u T W
    rw [single_show,Equiv.symm_apply_apply]; rfl
  have hL : mapW (lawNu p N v.t (fun _ => q)) W=rackWave (ownMap v.t (fun _ => q)) N :=
    lawNu_rack ..
  obtain ⟨he,he'⟩ := solo_data v x m q hj h
  have hR : mapW (raw m N) T=rackStation (ownMap v.t (fun _ => q)) N := by
    rw [←he']; exact law_peekR (g:=g) m hN he he
  have h1 : avg (lawOmega p N (v.t ()) q) f = avg (rackWave (ownMap v.t (fun _=>q)) N) u := by
    rw [←hL,←soloprice,mapW_avg,mapW_avg]
    unfold u; simp_rw [Equiv.symm_apply_apply]; rfl
  have h2 : avg (raw m N) (f ∘ v.desc x)=avg (rackStation (ownMap v.t (fun _=>q)) N) u := by
    rw [←hR,mapW_avg]; simp_rw [ht]; rfl
  rw [h2,h1]; exact compare_station _ u (fun i=>hf _) k hk hK
end Template
end HadwigerCounterexample

end

end OAI
