import OAI.Combinatorics.HadwigerCounterexample.PredictionExactification
import OAI.Combinatorics.HadwigerCounterexample.UltrafilterRates
import OAI.Combinatorics.HadwigerCounterexample.RefinedPinImages

namespace OAI

/-! # Prediction Classes -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset
open scoped BigOperators Topology

inductive PredictionClass
| dusk
| dawn (i : Bool)
| twinned
| noon
deriving Inhabited, DecidableEq

variable {p : Shape}
namespace PredictionClass

def active : PredictionClass→Bool→ Prop
| dusk,_=>False
| dawn i,j=>i=j
| twinned,_=>True
| noon,_=>True

def echoes (c : PredictionClass) (i j : Bool) (s r : F) :=
  ((s=1 ∧ c.active i) ↔ (r=1 ∧ c.active j)) ∧
    ((s=1 ∧ c.active i) → (i=j ∨ c=twinned))

def firstBit (α : Party) (i : Bool) := 1+α i

def lit (c : PredictionClass) (α : Party) :=
  (∀ i,¬c.active i → firstBit α i=0) ∧
    (c=twinned → α true=α false)

def assembly {N} (g : Bool→Augur p N) (i j : Bool) (s t : F) : Augur p N :=
  fun l q x => s*g i l q x+t*g j l q x

/-- Enough to test against dual relations. -/
def recital (c : PredictionClass) (p : Shape) {N}
    (g : Bool→Augur p N) (α : Party) (τ : ℝ) :=
  c.lit α ∧ ∀ (i j : Bool) (s t r : F), s*firstBit α i=t*firstBit α j →
    (∀ l q,tabRef p l q (assembly g i j s t) r ≤ τ) → c.echoes i j s t
abbrev season (p : Shape) (M : ℕ) := (n : ℕ)→Augur p (M*n)
def disappearing (U : Ultrafilter ℕ) {M} (g : season p M) (s : F) :=
  ∀ l q, slight (U:Filter ℕ) (fun i=>tabRef p l q (g i) s)

private def modest (U : Ultrafilter ℕ) {M}
    (g : Bool→season p M) (α : Party) (i : Bool) :=
  firstBit α i=0 ∧ ∃ s,g i |> fun x=> disappearing U x s

private def accords (U : Ultrafilter ℕ) {M}
    (g : Bool→season p M) (α : Party) :=
  α true=α false ∧ ∃ s, disappearing U
    (fun n : ℕ=>fun l q x => g true n l q x+g false n l q x) s

private def census (U : Ultrafilter ℕ) {M}
    (g : Bool→season p M) (α : Party) :=
  open scoped Classical in
  if modest U g α true then if modest U g α false then dusk else dawn false
  else if modest U g α false then dawn true
  else if accords U g α then twinned else noon

variable {U : Ultrafilter ℕ} {M : ℕ}
  {g : Bool → season p M} {α : Party}

private theorem census_active (i : Bool) :
    active (census U g α) i ↔ ¬modest U g α i := by
  classical
  unfold census
  cases i <;> split_ifs <;> simp_all [active]

private theorem census_lit :
    (census U g α).lit α := by
  classical
  constructor
  · intro i hi; exact (show modest U g α i from not_not.mp (fun h=> hi ((census_active i).mpr h))).1
  unfold census
  intro h; split_ifs at h; try contradiction
  exact ‹accords U g α›.1

theorem disappearing_add {x y : season p M} {r s : F}
    (h : disappearing U x r) (hh : disappearing U y s) :
    disappearing U (fun i => fun l q j=> x i l q j+y i l q j) (r+s) := by
  intro l q ε he
  filter_upwards [h l q _ (half_pos he),hh l q _ (half_pos he)] with i hi hj
  let v := lawOmega p (M*i) l q
  have hv (j : AtomKey (p:=p) l (M*i)) : 0≤ v j := by
    exact (unifOn_sub _).nz _
  let P j := x i l q j≠r*q
  let Q j := y i l q j≠s*q
  have hh (j) (h : x i l q j+y i l q j≠ (r+s)*q) : P j∨ Q j := by
    unfold P Q
    rw [add_mul] at h; contrapose h
    push Not at *
    simp [h]
  have hf : pr v P ≤ ε/2 := hi; have hg : pr v Q ≤ ε/2 := hj
  exact ((pr_mono hv hh).trans (pr_or_le hv)).trans (by linarith only [hf,hg])

private theorem census_match (h : accords U g α) :
    modest U g α true ↔ modest U g α false := by
  classical
  let x : season p M := fun n l q i=>g true n l q i+g false n l q i
  obtain ⟨hd,s,hs⟩:=h
  have hs : disappearing U x s := hs
  refine ⟨fun ⟨h,r,hg⟩=>⟨by simpa only [firstBit,←hd] using h,r+s,?_⟩,
    fun ⟨h,r,hg⟩=>⟨by simpa only [firstBit,hd] using h,r+s,?_⟩⟩
  · have he : (fun n l q j=>g true n l q j+x n l q j)=g false := by
      funext n l q j; change _+(_+_)=_; rw [←add_assoc,char_two,zero_add]
    rw [←he]; exact disappearing_add hg hs
  have he : (fun n l q j=>g false n l q j+x n l q j)=g true := by
    funext n l q j; change _+(_+_)=_; rw [add_left_comm,char_two,add_zero]
  rw [←he]; exact disappearing_add hg hs

set_option maxHeartbeats 1000000 in
private theorem census_echoes (i j : Bool) (s t r : F) (h : s*firstBit α i=t*firstBit α j)
    (hg : disappearing U (fun n=>assembly (fun i=>g i n) i j s t) r) :
    (census U g α).echoes i j s t := by
  classical
  unfold echoes; simp_rw [census_active]
  rcases bit_cases s with hs|hs <;> rcases bit_cases t with ht|ht <;> subst s t
  · simp
  · have hi : firstBit α j=0 := by simpa only [zero_mul,one_mul] using h.symm
    have hh : (fun n : ℕ=> assembly (fun i=>g i n) i j 0 1)=g j := by
      funext n l q x; change (0:F)*g i n l q x+ (1:F)*g j n l q x=g j n l q x; rw [one_mul,zero_mul,zero_add]
    have he : modest U g α j := ⟨hi,r,hh ▸ hg⟩
    simp [he]
  · have hi : firstBit α i=0 := by simpa only [zero_mul,one_mul] using h
    have hh : (fun n : ℕ=> assembly (fun i=>g i n) i j 1 0)=g i := by
      funext n l q x; change (1:F)*g i n l q x+ (0:F)*g j n l q x=g i n l q x; rw [one_mul,zero_mul,add_zero]
    have he : modest U g α i := ⟨hi,r,hh ▸ hg⟩
    simp [he]
  simp only [true_and]
  by_cases hv : i=j
  · subst j; simp
  have ht : accords U g α := by
    have hh : 1+α i=1+α j := by simpa only [one_mul,firstBit] using h
    have h : α i=α j := add_left_cancel hh
    let x1 (i j: Bool) := fun n=>assembly (fun i=>g i n) i j 1 1
    let x2 : season p M := fun n l q v=> g true n l q v+g false n l q v
    have hv' : x1 i j=x2 := by
      funext n l q v
      unfold x1 assembly x2
      simp only [one_mul]
      cases i <;> cases j <;> first | rfl | contradiction | exact add_comm _ _
    refine ⟨?_,r,show disappearing U x2 r from hv' ▸ (show disappearing U (x1 i j) r from hg)⟩
    cases i <;> cases j <;> first | contradiction | exact h | exact h.symm
  have hm := census_match ht
  by_cases he : modest U g α true
  · have hh (i : Bool) : modest U g α i := by cases i; exact hm.mp he; exact he
    simp [hh]
  have hh (i: Bool) : ¬modest U g α i := by cases i; exact mt hm.mpr he; exact he
  simp only [census, ite_eq_right (hh _), ite_eq_left ht]; simp [hh]

private theorem eventual_echoes (i j : Bool) (s t r : F) :
    ∃ τ:ℝ,0<τ ∧ ∀ᶠ n in U,
    s*firstBit α i=t*firstBit α j →
      ((∀ l q,tabRef p l q (assembly (fun i=> g i n) i j s t) r ≤ τ) →
        (census U g α).echoes i j s t) := by
  classical
  by_cases hf : disappearing U (fun n=>assembly (fun i=>g i n) i j s t) r
  · exact ⟨1,zero_lt_one,.of_forall (fun _ h _=> census_echoes i j s t r h hf)⟩
  unfold disappearing slight at hf
  push Not at hf
  obtain ⟨l,q,τ,hτ,h⟩:=hf
  exact ⟨τ,hτ,h.mono fun i hi _ H=>(hi.not_ge (H l q)).elim⟩

theorem examine (U : Ultrafilter ℕ) (p : Shape) (M : ℕ) (g : Bool→ season p M) (α : Party) :
    ∃ (c : PredictionClass) (τ : ℝ),0 < τ ∧
       (∀ᶠ n in U,c.recital p (fun i=>g i n) α τ) ∧ c.lit α ∧
       (c=dusk → ∀ i, ∃ r,disappearing U (g i) r) := by
  classical
  let A:=Bool × Bool × (F×F×F)
  let c:= census U g α
  choose τ hτ hg using fun x : A=> @eventual_echoes p U M g α
    x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2
  have hh : ∃ δ:ℝ,0<δ∧∀ x,δ≤τ x := by
    let S := univ.image τ
    have hn : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
    refine ⟨S.min' hn, ?_, fun x=> Finset.min'_le _ _ (mem_image_of_mem _ (mem_univ _))⟩
    obtain ⟨x,hx,hx'⟩:= mem_image.mp (Finset.min'_mem _ hn)
    exact hx' ▸ hτ x
  obtain ⟨δ,hδ,hT⟩:=hh
  refine ⟨c,δ,hδ,?_,census_lit,fun h i=>?_⟩
  · filter_upwards [eventually_all.mpr hg] with n h
    refine ⟨census_lit,fun i j s t r he hh=>?_⟩
    exact h (i,j,s,t,r) he (fun l q=>(hh l q).trans (hT _))
  have he : ¬ c.active i := by rw [h]; exact not_false
  exact (show modest U g α i from not_not.mp (fun h=>he ((census_active i).mpr h))).2
end PredictionClass
end HadwigerCounterexample

end

end OAI
