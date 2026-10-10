import OAI.Combinatorics.HadwigerCounterexample.PointAtomVanishing
import OAI.Combinatorics.HadwigerCounterexample.UnaryPositivityBounds

namespace OAI

/-! # Common Predictions -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset Submodule
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

abbrev Augur (p : Shape) (N : ℕ) := ∀ t : Tag p.g,F→AtomKey (p:=p) t N→F
def mismatch (p : Shape) {n N : ℕ} (g : Augur p N) (F : Pdual p n) (l : Tag p.g)
    (s : Label p.b) (f : Flavor p.g) (x : Orient p n N) (y : Knobs p.g n) :=
  F (useAtom p l s f y)≠ g l (dialed p l f y) (keyOne p l s (lit f l y) x)
def postulates (p : Shape) (o : Orient p n N)
    (g : Augur p N) (w : Pdual p n) (E : Finset (Label p.b)) (δ : ℝ) :=
  ∀ s,s∉E→∀ l f, pr (spins p n) (fun i => mismatch p g w l s f o i)≤δ

def yoke (p : Shape) (m : Mixer p n) (x : UnitType p n N) (i : Bool)
    (u : Profile p n) (α : F) : Pdual p n :=
  innerP p x i + (Tsym m u + α • role p n)

def claimed (p : Shape) (x : UnitType p n N)
    (g : Bool→Augur p N) (m : Mixer p n)
    (w : Bool→Profile p n) (α : Bool→F) (L : Bool → Finset (Label p.b)) (δ : ℝ) :=
  ∀ i,postulates p (onSide x i) (g i) (yoke p m x i (w i) (α i)) (L i) δ

def silent (w : Pdual p n) := ∀ x, x∈Xspace p n → w x=0

def fixStar (p : Shape) (n : ℕ) (l : Tag p.g) :
    Moment p n →ₗ[F] Profile p n :=
  cut p n ∘ₗ LinearMap.single F (fun _ : Tag p.g => Moment p n) l
theorem fix_one (p : Shape) (n : ℕ) (l : Tag p.g) (s : Label p.b) (z : Base p.g n) :
    atom p l s z=fixStar p n l (mom p s z) := rfl

theorem atom_silent {w : Pdual p n}
    (h : ∀ l s z,allows l z → w (atom p l s z)=0) : silent w := by
  classical
  intro x hx
  obtain ⟨u,hu,rfl⟩ := mem_X.mp hx
  have he l : Wtag p n l≤LinearMap.ker (w∘ₗfixStar p n l) := by
    refine Submodule.span_le.mpr ?_
    rintro x ⟨s,z,hz,rfl⟩
    exact h l s z hz
  have ht : (cut p n u)=∑ i : Tag p.g,fixStar p n i (u i) := by
    have hh := Finset.univ_sum_single u
    unfold fixStar
    simp_rw [LinearMap.comp_apply, ← map_sum (cut p n)]
    exact congrArg (cut p n) (Eq.symm hh)
  rw [ht,map_sum]; exact Finset.sum_eq_zero fun i _=>he _ (hu i)

theorem shared_base (p : Shape) (hn : 2*p.r≤n) (hr : 1 ≤ p.r) (hg : 0 < p.g) :
    ∃ (z : Base p.g n) (s : Label p.b), (∀ l, allows l z) ∧ eta p n (mom p s z)=1 := by
  classical
  let l : Tag p.g := ⟨0,hg⟩
  let f : Flavor p.g:= Flavor.sharedOnly
  let i := (Sum.inr () : ProbeIdx p.g)
  let v : Digest p.g := Pi.single i 1
  have hx : v.feasible l f := by
    rintro (x|⟨⟩) _
    · exact Pi.single_eq_of_ne (by simp [i]) _
    exact (‹¬_› trivial).elim
  have he := exists_of_pr_pos (spins_law p n).nz
    ((scanPrice_pos p).trans_le (scan_fraction (n:=n) l f v hr hn hx))
  obtain ⟨x,h,_⟩ := he
  refine ⟨lit f l x,0,fun i d t h k => ite_eq_right (by simp [f,Flavor.keeps]),?_⟩
  rw [←etaScan,h]; simp [v,Digest.sumBit,Digest.diagO,i]

theorem atom_union (p : Shape) (n : ℕ) (z : Base p.g n) (s : Label p.b) :
    ∑ i:Tag p.g,atom p i s z=0 := by
  simp_rw [atom,←map_sum (cut p n)]
  rw [Finset.univ_sum_single (fun i : Tag p.g => mom p s z)]
  funext x
  exact char_two (mom p s z)

set_option maxHeartbeats 800000 in
theorem exact_vat (w : Pdual p n) (E : Finset (Label p.b)) (g : F)
    (hE : (E.card:ℝ)<bp ((p.b:ℝ)-2*p.j))
    (hj : Odd p.g) (hn : 2*p.r≤n) (hr : 1≤p.r)
    (h : ∀ l s,s∉E → pr (spins p n)
      (fun x => w (useAtom p l s Flavor.full x)≠g *dialed p l Flavor.full x)<1/4) :
    g=0∧ silent w := by
  classical
  let Q l := w ∘ₗ fixStar p n l - g • eta p n
  have hi (l : Tag p.g) (s : Label p.b) (z : Base p.g n) :
      Q l (mom p s z)= w (atom p l s z)-g*eta p n (mom p s z) := rfl
  have hh (l s z) (hz : allows l z) : Q l (mom p s z)=0 := by
    have he (s) (hs : s∉E) :
        pr (spins p n) (fun x=> Q l (mom p s (lit Flavor.full l x))≠0)<1/4 := by
      simp_rw [hi,←etaScan p l s Flavor.full]
      simpa only [sub_ne_zero,useAtom,dialed] using h l s hs
    exact vat_excluded z E (Q l) (fun i h=>vat_erase l i (Q l) (he i h) z hz) hE s
  simp_rw [hi] at hh
  have he l s z (h : allows l z) : w (atom p l s z) =g*eta p n (mom p s z) :=
    sub_eq_zero.mp (hh l s z h)
  obtain ⟨z,s,hz,hb⟩ := shared_base p hn hr (by obtain ⟨_,hh⟩ := hj; omega)
  have h0 : g=0 := by
    have ht : w (∑ l:Tag p.g,atom p l s z)=0 := by rw [atom_union,map_zero]
    rw [map_sum] at ht
    simp_rw [he _ s z (hz _),hb,mul_one] at ht
    simpa only [Finset.sum_const, Finset.card_univ,Tag,Fintype.card_fin,
      odd_smul_bit hj] using ht
  refine ⟨h0,atom_silent (fun i s z h=> (he i s z h).trans ?_)⟩
  rw [h0,zero_mul]
end HadwigerCounterexample

end

end OAI
