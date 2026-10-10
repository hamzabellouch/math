import OAI.Geometry.SurfaceImmersion.Geometry.FinitePointNeighborhoods
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

/-! Finite distinct interior parameters have disjoint compact interval
windows, in their original order. -/
noncomputable section
open Set Filter
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {ι : Type*} [Finite ι]

theorem finite_corner_windows (T : ι → ℝ) (hi : Function.Injective T)
    (hT : ∀ i, T i ∈ Ioo (0:ℝ) 1) :
    ∃ a b : ι → ℝ, (∀ i, 0 < a i ∧ a i < T i ∧ T i < b i ∧ b i < 1) ∧
      Pairwise (fun i j => Disjoint (Icc (a i) (b i)) (Icc (a j) (b j))) ∧
      ∀ i j, T i < T j → b i < a j := by
  obtain ⟨U,hU,hdis⟩ := finite_disjoint_open_neighborhoods T hi
    (fun _ => Ioo (0:ℝ) 1) (fun _ => isOpen_Ioo) hT
  have hchoice : ∀ i, ∃ a b : ℝ, 0 < a ∧ a < T i ∧ T i < b ∧ b < 1 ∧ Icc a b ⊆ U i := by
    intro i
    obtain ⟨l,r,⟨hlt,htr⟩,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp ((hU i).1.mem_nhds (hU i).2.1)
    obtain ⟨a,hla,hat⟩ := exists_between hlt
    obtain ⟨b,htb,hbr⟩ := exists_between htr
    have hs : Icc a b ⊆ U i := fun _ hx => hsub ⟨hla.trans_le hx.1,hx.2.trans_lt hbr⟩
    have hab : a ≤ b := (hat.trans htb).le
    exact ⟨a,b,((hU i).2.2 (hs (left_mem_Icc.mpr hab))).1,hat,htb,
      ((hU i).2.2 (hs (right_mem_Icc.mpr hab))).2,hs⟩
  choose a b ha haT hTb hb hsub using hchoice
  have hd : Pairwise (fun i j => Disjoint (Icc (a i) (b i)) (Icc (a j) (b j))) :=
    fun i j hij => (hdis hij).mono (hsub i) (hsub j)
  refine ⟨a,b,fun i => ⟨ha i,haT i,hTb i,hb i⟩,hd,?_⟩
  intro i j hij
  have hne : i ≠ j := fun he => (ne_of_lt hij) (congrArg T he)
  by_contra hn
  have hji : a j ≤ b i := le_of_not_gt hn
  by_cases haij : a i ≤ a j
  · exact disjoint_left.mp (hd hne) ⟨haij,hji⟩ ⟨le_rfl,(haT j).le.trans (hTb j).le⟩
  · have haj : a j ≤ a i := (lt_of_not_ge haij).le
    have hai : a i ≤ b i := (haT i).le.trans (hTb i).le
    have hbaj : a i ≤ b j := ((haT i).trans hij |>.trans (hTb j)).le
    exact disjoint_left.mp (hd hne) ⟨le_rfl,hai⟩ ⟨haj,hbaj⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
