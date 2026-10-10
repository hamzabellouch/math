import OAI.Combinatorics.HadwigerCounterexample.BasisConditioning

namespace OAI

/-! # Unary Positivity Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace Template
variable (v : Solo p)

def patrol (m : Mixer p n) (w : Wgt (Knobs p.g n))
    (S : AtomKey (p:=p) (v.t ()) N→Prop) (K : ℕ) (q : F) (x : Orient p n N) :=
  luminous v m w S K x ∧
    3/4*pr (lawOmega p N (v.t ()) q) S ≤ pr w (offBeat v S x)

variable {K s : ℕ}
set_option maxHeartbeats 1200000 in
theorem patrolled (v : Solo p) (M : ℕ) (hM : 1≤M) (hg : Odd p.g) (hj : 1≤p.j)
    (z : Digest p.g) (hz : z.feasible (v.t ()) (v.f ())) (hr : 1≤p.r)
    (η : ℝ) (hη : 0<η)
    (hs : 2*profileA p K<s) (hG : bp (-((p.J-s:ℕ):ℝ))*bp s < glintRate K) :
    ∀ᶠ n : ℕ in atTop, let N := M*n
    let w:=scopedScan p n (v.t ()) (v.f ()) z; let q:=z.sumBit
    ∀ m : Mixer p n, unaryGood m K s →2*num (Full p n)<N →
    ∀ S,η ≤ pr (lawOmega p N (v.t ()) q) S →
    pr (raw m N) (fun x => ¬ patrol v m w S K q x) ≤ bp (-(1/16:ℝ)*n) := by
  classical
  let δ := 3/4*η; have hδ : 0<δ := by positivity
  let ε := η/4; have hε : 0<ε := by positivity
  filter_upwards [radiance_calendar v hs hg δ _ hδ hG,
    flat_recital v M hM hj ε hε,eventually_ge_atTop (2*p.r),
    pay_nat (a:=1/8) (b:=1/16) 2 (by norm_num)]
    with n hn hF hU ha N w q m hm hN S hS
  let μ := raw m N
  have hμ : IsLaw μ := raw_law m hN
  let P := offBeat (n:=n) v S
  let T (i : AtomKey (p:=p) (v.t ()) N) := ind (S i)
  have hw : IsLaw w := scanLaw p _ _ _ hr hU hz
  have he :
      carried w (fun x => dialed p (v.t ()) (v.f ()) x=q) := fun i hi => by
    unfold w scopedScan; rw [onW_val,ind_zero (show ¬ _ from fun h =>
      hi (congrArg Digest.sumBit h)),mul_zero,zero_div]
  have ht (x) : |T x|≤1 := by rw [abs_of_nonneg (ind_nonneg (S x))]; exact ind_le_one _
  have hx := hF m w q hw he (scopedZ_scan p n _ _ _ hw) hN T ht
  have hy := hn N hN m hm w hw (scanned_flow p n (v.t ()) (v.f ()) z) S
  let b := pr (lawOmega p N (v.t ()) q) S
  let X (x) := ε ≤ |pr w (P x)-b|
  let Y (x) := ∃ i, 0<totalRank i ∧ totalRank i≤K ∧ glow v m w S (glintRate K) δ i x
  have hi i (h : ¬patrol v m w S K q i) : X i ∨ Y i := by
    by_contra! hh
    have hr : 3/4*b≤pr w (P i) := by
      have ht := lt_of_not_ge hh.1
      change |pr w (P i)-b|<ε at ht
      have hz := (abs_lt.mp ht).1
      unfold ε at *; change η≤b at hS; linarith only [hz,hS]
    have hd : δ ≤ pr w (P i) := le_trans (mul_le_mul_of_nonneg_left hS (by norm_num)) hr
    exact h ⟨glow_luminous v m w hw S K i δ hδ hd (fun z h1 h2 h3 => hh.2 ⟨z,h1,h2,h3⟩),hr⟩
  apply (le_trans (pr_mono hμ.nz hi) (pr_or_le hμ.nz)).trans
  have h1 : pr μ X≤ bp (-(1/8:ℝ)*n) := le_trans (le_of_eq (by
    unfold X P b minorCall offBeat T; simp only [pr]; rfl)) hx
  apply (add_le_add h1 hy).trans
  have he : (1:ℝ) ≤ profileA p K := by
    have hi : 1≤psize p := Fintype.card_pos_iff.mpr ⟨emptySel⟩
    have hP : 0 < profileA p K := by unfold profileA; exact Nat.mul_pos (Nat.mul_pos (by omega) hi) (by omega)
    exact_mod_cast (show 1≤profileA p K from hP)
  rw [two_mul] at ha
  refine le_trans ?_ ha
  gcongr; linarith

def basebeta (p : Shape) (K : ℕ) :=
  bp (-((K^2:ℕ):ℝ)-1)* scanPrice p

theorem basebeta_pos (p : Shape) (K : ℕ) : 0<basebeta p K :=
  mul_pos (bp_pos _) (scanPrice_pos _)

set_option maxHeartbeats 800000 in
theorem patrol_beta (v : Solo p)
    (S : AtomKey (p:=p) (v.t ()) N→ Prop) (m : Mixer p n) (K : ℕ)
    (z : Digest p.g) (hz : z.feasible (v.t ()) (v.f ())) (hr : 1 ≤ p.r) (hn : 2*p.r≤n)
    (o : Orient p n N) :
    let l := v.t (); let t := v.f (); let q := z.sumBit
    let u := lawOmega p N l q
    patrol v m (scopedScan p n l t z) S K q o →
    ∀ d : ℕ,d≤ K^2 → ∀ f : Vec (Fin d)→ₗ[F] Profile p n,
      Injective f → (∀ x,totalRank (f x)≤K) → ∀ x,
      basebeta p K*pr u S ≤
        pr (scopedBit p n l t q) (fun i=> (scan p l t i=z∧ (offBeat v S o) i) ∧ stains v m f i=x) := by
  classical
  intro l t q u h d hd f hf hx x
  let Q := offBeat v S o; let F (j : Knobs p.g n) := scan p l t j=z
  let w := spins p n; let R (j : Knobs p.g n) := dialed p l t j=q
  let v' := onW w F
  have hw := spins_law p n
  have hv' := scanLaw (n:=n) p l z t hr hn hz
  let Z i := stains v m f i=x
  let A := pr u S; let a := pr v' Q
  have hA : 0 ≤ A := pr_nonneg (unifOn_sub _).nz
  obtain ⟨⟨ha,hh⟩,he⟩ := h
  specialize hh d hd f hf hx x
  have ht : ∀ i,(F i ∧ Q i)∧Z i → R i := fun i h=> congrArg Digest.sumBit h.1.1
  let B := fun i=> (F i ∧ Q i) ∧ Z i
  have hi : pr w B=pr w F*(a * pr (onW v' Q) Z) := by
    rw [show B=(fun i => F i ∧ Q i∧Z i) from funext fun i=>propext and_assoc]
    rw [pr_of_on hw.nz F]; congr 1
    exact pr_of_on hv'.nz Q Z
  have hY : 0 < pr w R :=
    (scanPrice_pos _).trans_le (dial_fraction p n l t q hr hn ⟨z,hz,rfl⟩)
  have hL : (7/8:ℝ)*bp (- (d:ℝ)) ≥ 7/8*bp (- ((K^2:ℕ):ℝ)) :=
    mul_le_mul_of_nonneg_left (bp_le (by exact_mod_cast neg_le_neg (by exact_mod_cast hd :
      (d:ℝ)≤((K^2:ℕ):ℝ)))) (by norm_num)
  change _≤pr (onW w R) B
  have hR : pr w B≤ pr (onW w R) B := by
    rw [pr_on,show (fun x=> R x∧ B x)= B from funext fun i=>propext ⟨And.right,fun h=>⟨ht i h,h⟩⟩]
    exact (by
      rw [le_div_iff₀ hY]
      have hh := (pr_le_tot (p:=R) hw.nz).trans hw.total.le
      exact (mul_le_mul_of_nonneg_left hh (pr_nonneg hw.nz)).trans_eq (mul_one _))
  apply le_trans ?_ hR
  rw [hi]; unfold basebeta; rw [bp_sub,bp_one]
  let K' := bp (-((K^2:ℕ):ℝ))
  have hg : scanPrice p*( (3/4*A)*(7/8*K')) ≤ pr w F*(a * pr (onW v' Q) Z) :=
    mul_le_mul (scan_fraction l t z hr hn hz)
      (mul_le_mul he (le_trans hL hh) (mul_nonneg (by norm_num) (bp_pos _).le) ha.le)
      (mul_nonneg (mul_nonneg (by norm_num) hA) (mul_nonneg (by norm_num) (bp_pos _).le))
      (pr_nonneg hw.nz)
  refine le_trans ?_ hg
  change K' / 2 * _ * _ ≤ _
  nlinarith only [mul_nonneg (mul_nonneg (scanPrice_pos p).le
    (show 0≤K' from (bp_pos _).le)) hA]

end Template
end HadwigerCounterexample

end

end OAI
