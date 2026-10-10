import OAI.Combinatorics.HadwigerCounterexample.FrameIntersectionCosts
import OAI.Combinatorics.HadwigerCounterexample.CellPruning

namespace OAI

/-! # Supported Phase Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ} {T : Cov p N}

/-- Tables already fixed on population. bag M is total for convenience
but hypotheses on positive mass only apply on the indicated chart. -/
structure Bazaar (p : Shape) {N} (n r : ℕ) (T : Cov p N) where
  ix : UnitType p n N → Atlas p r T
  bag : (M : Atlas p r T) → Bool → UnitType p n N → Batch M N

namespace Bazaar

variable (s : Bazaar p n r T)

def opened (Δ : UnitType p n N → Ambient p N) (w : Wgt (UnitType p n N)) :=
  ∀ x,w x≠0 → standard (s.ix x) ∧ ∀ i,compFor (s.ix x)
    (s.bag (s.ix x) i x) (imageP p x i) (Δ x)

def chart (w : Wgt (UnitType p n N)) (M : Atlas p r T) :=
  subW w (fun x => s.ix x=M)

theorem active {Δ : UnitType p n N→Ambient p N} {w} {M}
    (h : s.opened Δ w) (x) (hx : s.chart w M x≠0) :
    s.ix x=M ∧ standard M ∧ ∀ i,compFor M (s.bag M i x) (imageP p x i) (Δ x) := by
  have h' : s.ix x=M := Classical.byContradiction fun he => hx (subW_carried w _ _ he)
  refine ⟨h',?_⟩
  subst M; exact h x (left_ne_zero_of_mul hx)

def pay (M G : Atlas p r T) (j : Bool) (S : Party)
    (y : UnitType p n N) : Batch M N × Batch G N :=
  (thermal p y S (src M),s.bag G j y)

end Bazaar

def loseA (_ : Shape) (N x y : ℕ) := bp (-((x:ℝ)+y)*N+0.01*N)
def prize (_ : Shape) (N x : ℕ) := bp (- ((x:ℝ)+0.5)*N)
def beat (N : ℕ) := bp (-0.245*N)
def selPrice (p : Shape) (r n N : ℕ) (H ε : ℝ) :=
  ∀ x y : ℕ,x≤2*r → y≤2*r → H*heatRate p n N ε x y≤loseA p N x y

namespace Bazaar
variable {s : Bazaar p n r T}

theorem bag_rate (m : Mixer p n) {H : ℝ} (hH : 0≤H)
    {w : Wgt (UnitType p n N)} {Δ} {ε : ℝ} (hm : IsLaw (raw m N)) (he : initCap p N m ε)
    (hv : SubLaw w) (hw : bySide p w m H)
    (hl : s.opened Δ w) (hp : selPrice p r n N H ε)
    (M : Atlas p r T) (i : Bool) :
    ∀ x, mapW (s.chart w M) (s.bag M i) x ≤ loseA p N (cells M) 0 := by
  classical
  intro x
  let v := s.chart w M
  have hV : SubLaw v := subLaw_sub hv _
  by_cases hx : standard M
  · refine le_trans (pr_on_mono hV.nz (P:=fun y => s.bag M i y=x)
      (Q:=fun y => basisFrom p y i x) (fun z hz hg => ?_)) ?_
    · subst x
      exact ((active s hl z hz).2.2 i).1
    refine (pr_mono_left (subW_le hv.nz _) _).trans ?_
    exact (heat_none i x hH m hm he hw).trans (hp (cells M) 0 hx.2.1 (Nat.zero_le _))
  have h : v=(fun _ => 0) :=
    funext fun x => Classical.byContradiction fun h => hx (active s hl x h).2.1
  change mapW v _ _≤_
  rw [h]
  simp only [mapW,pr,avg,zero_mul,Finset.sum_const_zero]
  exact (bp_pos _).le

theorem glimpse_prize (m : Mixer p n) {H : ℝ} (hH : 0≤H)
    {w : Wgt (UnitType p n N)} {Δ} {ε : ℝ}
    (hm : IsLaw (raw m N)) (he : initCap p N m ε) (hv : SubLaw w)
    (hw : bySide p w m H) (h : s.opened Δ w) (hp : selPrice p r n N H ε)
    (M G : Atlas p r T) (i : Bool) (hh : standard M) (hh' : standard G)
    (P : UnitType p n N → Prop)
    (hf : ∀ x, s.chart w G x≠0 → P x → glimpse p x i (src M)) :
    ∀ x, mapW (subW (s.chart w G) P) (s.pay M G i (unary i)) x≤ prize p N (cells G) := by
  classical
  rintro ⟨x,y⟩
  let v := s.chart w G
  have hv' : SubLaw v := subLaw_sub hv _
  change pr (subW v P) _ ≤ _
  rw [pr_sub]
  refine (pr_on_mono hv'.nz (Q:=fun z =>
    basisFrom p z i y ∧ glimpse p z i (src M) ∧ thermal p z (unary i) (src M)=x) ?_).trans ?_
  · rintro z hz ⟨he,hx⟩
    have h1 : s.bag G i z=y := congrArg Prod.snd hx
    exact ⟨h1 ▸ ((active s h z hz).2.2 i).1,hf z hz he,congrArg Prod.fst hx⟩
  refine (pr_mono_left (subW_le hv.nz _) _).trans ?_
  apply (heat_one i (src M) x y hH m hm he hw).trans
  refine (hp (cells G) (cells M) hh'.2.1 hh.2.1).trans ?_
  unfold prize loseA
  apply bp_le
  have ht : (1:ℝ)≤cells M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hh.1
  rw [← add_mul]; apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  linarith

end Bazaar

variable {A B V : Type} [Fintype A] [Fintype B] [Fintype V]

private theorem write_weight (g : Wgt A) (w : Wgt A) (hw : SubLaw w) (f : A→B)
    (h : ∀ x, |g x|≤1) :
    ∃ t : Wgt B, (∀ x,|t x|≤1) ∧
    ∀ s : Wgt B, avg w (fun x => g x*s (f x))=avg (mapW w f) (fun y => t y*s y) := by
  classical
  let V (y : B) := onW w (fun x => f x=y)
  have hv (y) : SubLaw (V y) := normW_subLaw (subW_nonneg hw.nz _)
  let T (y) := avg (V y) g
  refine ⟨T,fun y => (abs_avg_le (hv y).nz).trans ((hv y).avg_le zero_le_one h),fun s => ?_⟩
  calc avg w (fun x => g x*s (f x))
    _ = avg (mixW (mapW w f) V) (fun x => g x*s (f x)) :=
      congrArg (avg · (fun x => g x*s (f x))) (disintegrate hw.nz f)
    _ = _ := by
      rw [mixW_avg]; refine avg_congr (fun x _ => ?_)
      calc _ = avg (V x) (fun y => g y*s x) := avg_congr (fun y hy => by
                 have h : f y=x := Classical.byContradiction fun h => hy
                   (normW_carried (subW_carried w (fun v => f v=x)) y h)
                 rw [h])
           _ = _ := avg_mul ..

theorem mapW_sub (f : A→B) {w : Wgt A} (hw : SubLaw w) : SubLaw (mapW w f) := by
  refine ⟨fun _ => pr_nonneg hw.nz,?_⟩
  have he := mapW_avg w f (fun _ => 1)
  rw [avg_const,avg_const,mul_one,mul_one] at he
  rw [he]; exact hw.total

variable [AddCommGroup V] [Module F V]

/-- Walsh bound on pushforward tuples with arbitrary separate
query weights. -/
theorem walsh_weighted (b : V →ₗ[F] V →ₗ[F] F) (hb : Function.Injective b)
    (w : Wgt A) (v : Wgt B) (hw : SubLaw w) (hv : SubLaw v)
    (f : A→V) (g : B→V) (S : Wgt A) (T : Wgt B) {p q : ℝ}
    (hs : ∀ x,|S x|≤1) (ht : ∀ x, |T x| ≤1)
    (hp : ∀ x, mapW w f x ≤ p) (hq : ∀ x,mapW v g x ≤ q) :
    (avg (pairW w v) (fun x => S x.1*T x.2 * wsign (b (f x.1) (g x.2))))^2 ≤ num V*p*q := by
  obtain ⟨Y,hY,hA⟩ := write_weight S w hw f hs
  obtain ⟨X,hX,hB⟩ := write_weight T v hv g ht
  have he :
      avg (pairW w v) (fun x => S x.1*T x.2*wsign (b (f x.1) (g x.2)))=
        avg (mapW v g) (fun y => X y* avg (mapW w f) (fun x =>
          Y x*wsign (b x y))) := by
    rw [pairW_avg,avg_avg]
    have he y :
        avg w (fun x => S x*T y* wsign (b (f x) (g y))) =
        T y * avg (mapW w f) (fun x => Y x*wsign (b x (g y))) := by
      have hh := hA (fun v => wsign (b v (g y)))
      simp_rw [mul_comm (S _) (T y),mul_assoc,avg_mul']
      rw [hh]
    simp_rw [he]
    exact hB (fun y => avg _ (fun x => Y x*wsign (b x y)))
  rw [he]
  exact walsh_mass b hb (mapW w f) (mapW v g) Y X hY hX (mapW_sub f hw) (mapW_sub g hv) hp hq

end HadwigerCounterexample

end

end OAI
