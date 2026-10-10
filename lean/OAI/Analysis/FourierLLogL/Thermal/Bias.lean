import OAI.Analysis.FourierLLogL.Thermal.Piece
import OAI.Analysis.FourierLLogL.Thermal.GridFreq

/-! # Extracting the biased spectrum -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate Real
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Thermal
open Law Node Period Real Compress.Params

variable {M l : ℕ}
open scoped Classical

def ball (A : Form M) (r : ℝ) : Finset (Grid M) := Finset.univ.filter fun i => delta A i ≤ r

lemma mem_ball (A : Form M) (r : ℝ) (x : Grid M) : x ∈ ball A r ↔ delta A x ≤ r := by simp [ball]

def fnear (A : Form M) (r R : ℝ) (x : Grid M) :=
    ∃ n, delta A n ≤ r ∧ rad (x-n) ≤ R

def separated {B : Type*} [DecidableEq B] (tag : B → Grid M) (A : Form M) (r R : ℝ)
    (s : Finset B) : Prop :=
    ∀ x∈s, ∀ y∈s, x≠y → ¬ fnear A r R (tag x-tag y)

def request (A : Form M) (j : ℕ) (p : Node) (a : Grid M → ℝ) (α b k : ℝ) :=
    ∃ s : Finset (Grid M), exp k ≤ (s.card:ℝ) ∧
      (∀ x∈s, high p a α A b x) ∧ separated id A (sepRad j) (sig j*p.invlen) s

/-- Bias tagged to subgroup characters χ_gx, side coordinate and the fixed child. -/
def biases (P : Law (Grid M)) (p : Node) (A : Form M) (hl : l ≤ M)
    (s : Finset (Grid l)) (B : Bool) (v : Grid l → Grid M → ℂ) (β : ℝ) :=
    (∀ i z, ‖v i z‖ ≤ 1) ∧ ∀ i∈s, β ≤ P.Ex (fun x =>
      if x ∈ (child p B).block M then
          (channel A x).Ex (fun z => (v i z * chi (raise hl i) x).re)
      else 0)

private lemma nearby_bias {p : Node} (hp : ok p M)
    {a : Grid M → ℝ} {P : Law (Grid M)} (hP : PieceLaw p a P)
    (A : Form M) (u i : Grid M) (B : Bool) {v : Grid M → ℂ} (hv : ∀ z, ‖v z‖ ≤ 1)
    (E : ℝ) (hE : rad (u-i) ≤ E * p.invlen) :
    let test (s : Grid M) (v : Grid M → ℂ) := P.Ex (fun x =>
      if x ∈ (child p B).block M then
          (channel A x).Ex (fun z => (v z * chi s x).re) else 0)
    ∃ w : Grid M → ℂ, (∀ z, ‖w z‖ ≤ 1) ∧ test u v -8*E ≤ test i w := by
  intro test
  let x' := p.start M
  let w (z : Grid M) := v z * chi (u-i) x'
  have hp0 : 0 ≤ E := nonneg_of_mul_nonneg_left ((rad_nonneg _).trans hE) p.invlen_pos
  have hn (z : Grid M) : ‖w z‖ ≤ 1 := by simp_rw [w,norm_mul,norm_chi,mul_one]; exact hv z
  have he (x : Grid M) (hx : 0 < P x) :
      (channel A x).Ex (fun z => (v z * chi u x).re) -8*E ≤
        (channel A x).Ex (fun z => (w z * chi i x).re) := by
    calc
      _ = (channel A x).Ex (fun z => (v z * chi u x).re-8*E) := by rw [Ex_sub,Ex_const]
      _ ≤ _ := Ex_mono _ fun z => by
        have hh := phase_distance (u-i) x x'
        have heq : ‖chi (u-i) x-chi (u-i) x'‖ ≤ 8*E := by
          apply le_trans hh
          calc
            _ ≤ E * p.invlen * (8 * p.len) := by
              have H := p.invlen_pos
              gcongr
              exact diam_block (piece_support hp hP _ hx) (start_mem hp.1 hp.2)
            _ = _ := by rw [rinv]; field_simp [p.len_pos.ne']
        have Hg : (v z*chi u x).re-(w z*chi i x).re ≤ 8*E :=
          calc
            _ = (v z*chi i x * (chi (u-i) x-chi (u-i) x')).re := by
              unfold w
              rw [show v z*chi i x * (chi (u-i) x-chi (u-i) x') =
                    v z*(chi (u-i) x * chi i x)-v z*chi (u-i) x'*chi i x by ring,
                ← chi_add',sub_add_cancel,Complex.sub_re]
            _ ≤ _ := by
              apply le_trans (le_abs_self _)
              apply le_trans (Complex.abs_re_le_norm _)
              rw [norm_mul,norm_mul,norm_chi,mul_one]
              exact (mul_le_of_le_one_left (by positivity) (hv z)).trans heq
        linarith
  refine ⟨w,hn,?_⟩
  unfold test
  rw [← Ex_const P (8*E),← Ex_sub]
  refine P.Ex_mono_mem fun x hx => ?_
  split_ifs
  · exact he x hx
  linarith

lemma extract_spectrum (j : ℕ) {A : Form M} {p : Node} {a : Grid M → ℝ} {α b k : ℝ}
    (hp : p.valid) (hv : p.lev < M)
    (ha : 0 ≤ a) (hα : 0 < α) {P : Law (Grid M)} (hP : PieceLaw p a P)
    (hm : 0 < p.avg a) (hm' : p.avg a ≤ 2*α)
    (he : 8*sig j ≤ b^2) (hr : request A j p a α b k) :
    let l := snapGrid j p M
    ∃ (s : Finset (Grid l)) (B : Bool) (v : Grid l → Grid M → ℂ),
      s.Nonempty ∧ k-log 2 ≤ log (s.card:ℝ) ∧
        separated (raise (snap_le _ _)) A (sepRad j) (sig j*p.invlen/2) s ∧
        biases P p A (snap_le _ _) s B v (b^2/100) := by
  classical
  intro l
  have hl := snap_le (M:=M) j p
  let g := down hl
  let d := raise hl
  let R := sig j*p.invlen
  let D := sepRad j
  obtain ⟨s,hs,hb,hr⟩ := hr

  let t := s.filter (fun x => b^2 ≤ energyZ p.L a α A x)
  have hh : ∃ B, ∃ t' ⊆ s, s.card ≤ 2*t'.card ∧
      ∀ x∈t', b^2 ≤ energyZ (p.child B) a α A x := by
    by_cases H : s.card ≤ 2*t.card
    · exact ⟨false,t,Finset.filter_subset _ _,H,fun i hi => (Finset.mem_filter.mp hi).2⟩
    · refine ⟨true,s \ t, Finset.sdiff_subset, ?_,?_⟩
      · have hh : t ⊆ s := Finset.filter_subset _ _
        rw [Finset.card_sdiff_of_subset hh]
        have hi := Finset.card_le_card hh; omega
      intro x hx
      obtain ⟨hx,hx'⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨B,hu⟩ := hb x hx
      cases B
      · exact (hx' (Finset.mem_filter.mpr ⟨hx,hu⟩)).elim
      · exact hu
  obtain ⟨B,t,ht,h1,h2⟩ := hh
  let U := t.image g
  have hp' : ok p M := ⟨hp,hv.le⟩
  have hX (x : Grid M) : rad (x-d (g x)) ≤ R/20 := (step_scale j hp'.2).2.2.2 x
  have hY (x) (hx : x∈s) (y) (hy : y∈s) (hne : x≠y) :
      ¬ fnear A D (R/2) (d (g x)-d (g y)) := by
    intro hn
    obtain ⟨i,hi,h⟩ := hn
    apply hr _ hx _ hy hne
    refine ⟨i,hi,?_⟩
    simp only [id_eq]
    rw [show x-y-i = (d (g x)-d (g y)-i)+(x-d (g x))+ -(y-d (g y)) by ring]
    apply le_trans (rad_add _ _)
    have hh := rad_add (d (g x)-d (g y)-i) (x-d (g x))
    rw [rad_even]
    linarith [hX x,hX y,rad_nonneg (x-d (g x))]
  have hi : Set.InjOn g s := by
    intro x hx y hy H
    by_contra he
    apply hY x hx y hy he
    refine ⟨0,?_,?_⟩
    · rw [delta_zero]; unfold D sepRad; positivity
    rw [H,sub_self,sub_self]
    have hh : 0 ≤ R := by have hhi := hX x; linarith [rad_nonneg (x-d (g x))]
    simpa [rad] using div_nonneg hh (by norm_num : (0:ℝ)≤2)
  have Hc : exp k ≤ 2*U.card := by
    rw [show U.card=t.card from Finset.card_image_of_injOn (hi.mono ht)]
    exact hs.trans (by exact_mod_cast h1)
  have Hc' : (0:ℝ) < U.card := by linarith [exp_pos k]
  have Hcp : 0 < U.card := by exact_mod_cast Hc'
  have hvv (i : Grid l) :
      ∃ v : Grid M → ℂ, (∀ z, ‖v z‖ ≤ 1) ∧ (i∈U →
        b^2/100 ≤ P.Ex fun x => if x∈(p.child B).block M then
          (channel A x).Ex fun z => (v z*chi (d i) x).re else 0) := by
    by_cases hh : i∈U
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hh
      obtain ⟨v,hv1,hv2⟩ := piece_child_bias hp hv ha hα hP hm hm' A x B (h2 x hx)
      obtain ⟨w,hw1,hw2⟩ := nearby_bias hp' hP A x (d (g x)) B hv1 (sig j/20)
        ((hX x).trans (by unfold R; rw [div_mul_eq_mul_div]))
      refine ⟨w,hw1,fun _ => ?_⟩
      dsimp only at hw2
      nlinarith
    exact ⟨fun _ => 0,fun _ => by simp, fun h => (hh h).elim⟩
  choose v hv1 hv2 using hvv
  refine ⟨U,B,v,Finset.card_pos.mp Hcp,?_,?_,hv1,hv2⟩
  · have hh := log_le_log (exp_pos k) Hc
    rw [log_exp,Real.log_mul (by norm_num) Hc'.ne'] at hh
    linarith
  intro i hi j hj he
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hj
  exact hY x (ht hx) y (ht hy) (fun h => he (congrArg g h))

end FourierLLogL.Dyadic.Thermal

end OAI
