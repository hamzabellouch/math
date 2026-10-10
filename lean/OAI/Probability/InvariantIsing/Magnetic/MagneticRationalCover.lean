import OAI.Probability.InvariantIsing.Magnetic.MagneticVariational
import Mathlib.Topology.Compactness.Compact

namespace OAI

/-! Every bounded magnetization profile is close to one of finitely many
rational interior profiles, including profiles at the boundary. -/
noncomputable section
open Set
open scoped Topology
namespace InvariantIsing

lemma exists_interior_rat_close {x δ : ℝ} (hx : |x|≤1) (hδ : 0<δ) :
    ∃ q : ℚ, |(q:ℝ)|<1 ∧ |x-(q:ℝ)|<δ := by
  have hl : max (-1:ℝ) (x-δ) < min 1 (x+δ) := by
    rw [max_lt_iff,lt_min_iff,lt_min_iff]
    constructor <;> constructor <;> linarith [(abs_le.mp hx).1,(abs_le.mp hx).2]
  obtain ⟨q,hq₁,hq₂⟩ := exists_rat_btwn hl
  refine ⟨q, abs_lt.mpr ⟨(le_max_left _ _).trans_lt hq₁,
    hq₂.trans_le (min_le_left _ _)⟩,?_⟩
  apply abs_lt.mpr
  constructor
  · have := hq₂.trans_le (min_le_right _ _)
    linarith
  · have := (le_max_right _ _).trans_lt hq₁
    linarith

lemma finite_rational_magnetization_cover {A : Type*} [Fintype A]
    {δ : ℝ} (hδ : 0<δ) :
    ∃ Q : Finset (RationalMagnetization A), Q.Nonempty ∧
      ∀ x : A → ℝ, (∀ a, |x a|≤1) →
        ∃ q∈Q, ∀ a, |x a-(q.val a:ℝ)|<δ := by
  classical
  let K : Set (A → ℝ) := Set.pi Set.univ (fun _ => Icc (-1:ℝ) 1)
  have hK : IsCompact K := by
    simpa only [K, Set.pi, Set.mem_univ, forall_const] using
      (isCompact_pi_infinite (s := fun _ : A => Icc (-1:ℝ) 1) (fun _ => isCompact_Icc))
  let U : RationalMagnetization A → Set (A → ℝ) :=
    fun q => {x | ∀ a, |x a-(q.val a:ℝ)|<δ}
  have ho (q : RationalMagnetization A) : IsOpen (U q) := by
    change IsOpen {x : A → ℝ | ∀ a, |x a-(q.val a:ℝ)|<δ}
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite (fun a => isOpen_lt ((continuous_apply a).sub continuous_const).abs continuous_const)
  have hcover : K ⊆ ⋃ q, U q := by
    intro x hx
    have hx' a : |x a|≤1 := abs_le.mpr (hx a (mem_univ a))
    choose q hq hd using fun a => exists_interior_rat_close (hx' a) hδ
    exact mem_iUnion.mpr ⟨(⟨q,hq⟩ : RationalMagnetization A),hd⟩
  obtain ⟨Q,hQ⟩ := hK.elim_finite_subcover U ho hcover
  have hzero : (fun _ : A => (0:ℝ))∈K := by intro a _; constructor <;> norm_num
  have hne : Q.Nonempty := by
    obtain ⟨q,hq⟩ := mem_iUnion.mp (hQ hzero)
    obtain ⟨hq,_⟩ := mem_iUnion.mp hq
    exact ⟨q,hq⟩
  refine ⟨Q,hne,?_⟩
  intro x hx
  have hxK : x∈K := by intro a _; exact abs_le.mp (hx a)
  obtain ⟨q,hq⟩ := mem_iUnion.mp (hQ hxK)
  obtain ⟨hq,hxq⟩ := mem_iUnion.mp hq
  exact ⟨q,hq,hxq⟩

end InvariantIsing

end

end OAI
