import OAI.Geometry.PeriodicTiling.Dependence
import Mathlib.GroupTheory.OrderOfElement

namespace OAI

noncomputable section

namespace PeriodicTilingThree

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def activeLabels (o : GraphOutputs E) (i : Channel p) (x : Plane) :
    Finset (Label p i) := by
  classical
  exact Finset.univ.filter (Active E o i x)

@[simp] theorem mem_activeLabels (o : GraphOutputs E) (i : Channel p)
    (x : Plane) (j : Label p i) :
    j ∈ activeLabels E o i x ↔ Active E o i x j := by
  classical
  simp [activeLabels]

def selectSymbol (S : Finset (Symbol p)) : Symbol p := by
  classical
  exact if h : S.Nonempty then h.choose else 1

theorem selectSymbol_mem
    {p : ℕ} [NeZero p]
    (S : Finset (Symbol p)) (hS : S.Nonempty) :
    selectSymbol S ∈ S := by
  classical
  simp only [selectSymbol, dite_eq_left hS]
  exact hS.choose_spec

def selectedWord (o : GraphOutputs E) : WordArray p :=
  fun n m => selectSymbol (activeLabels E o (.inl n) (0, m))

theorem selectedWord_active (o : GraphOutputs E)
    (hactive : ∀ n x, ∃ j, Active E o (.inl n) x j) (n : Column p) (m : ℤ) :
    Active E o (.inl n) (0, m) (selectedWord E o n m) := by
  apply (mem_activeLabels E o (.inl n) (0, m) _).mp
  apply selectSymbol_mem
  obtain ⟨j, hj⟩ := hactive n (0, m)
  exact ⟨j, (mem_activeLabels E o (.inl n) (0, m) j).mpr hj⟩

theorem selectedWord_active_at (o : GraphOutputs E) (hdep : HasDependence E o)
    (hactive : ∀ n x, ∃ j, Active E o (.inl n) x j) (n : Column p) (x : Plane) :
    Active E o (.inl n) x (selectedWord E o n (lineValue n x)) := by
  apply (active_ordinary_iff E hdep n (y := (0, lineValue n x))
    (by simp) _).mpr
  exact selectedWord_active E o hactive n _

theorem selectedWord_lineRule (o : GraphOutputs E) (hdep : HasDependence E o)
    (hactive : ∀ n x, ∃ j, Active E o (.inl n) x j)
    (hwords : ∀ x (w : Word p), (∀ n, Active E o (.inl n) x (w n)) → Allowed p w) :
    LineRule p (selectedWord E o) := by
  intro d e
  apply hwords (d, e)
  intro n
  simpa only [lineValue, mul_comm, add_comm] using
    selectedWord_active_at E o hdep hactive n (d, e)

theorem selectedWord_nonconstant_of_forced_letters
    (o : GraphOutputs E) (hdep : HasDependence E o)
    (hactive : ∀ n x, ∃ j, Active E o (.inl n) x j)
    (a b : Symbol p) (hab : a ≠ b) (x y : Plane)
    (hx : ∀ n j, Active E o (.inl n) x j → j = a)
    (hy : ∀ n j, Active E o (.inl n) y j → j = b) :
    NonconstantColumns (selectedWord E o) := by
  intro n
  refine ⟨lineValue n x, lineValue n y, ?_⟩
  have ha := hx n _ (selectedWord_active_at E o hdep hactive n x)
  have hb := hy n _ (selectedWord_active_at E o hdep hactive n y)
  intro he
  exact hab (ha.symm.trans (he.trans hb))

theorem graph_period_useful (o : GraphOutputs E) (v : Plane)
    (hv : Period (graph o) (v, (0 : V E))) (x : Plane) (k : Input E) :
    o.c (x + v, k) = o.c (x, k) := by
  have hm : point o (x, k) + (v, (0 : V E)) ∈ graph o :=
    (hv (point o (x, k))).mpr (point_mem_graph o (x, k))
  have he := eq_point_of_mem_graph o hm
  have hq : q0 E (point o (x, k) + (v, (0 : V E))) = (x + v, k) := by
    rw [map_add, q0_point]
    refine Prod.ext rfl ?_
    funext i
    simp [q0]
  rw [hq] at he
  funext i
  have hi := congrArg (fun z : Ambient E => (z.2.2 i).2) he
  simpa only [Prod.fst_add, Prod.snd_add, Pi.add_apply, point_c,
    Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, add_zero] using hi.symm

theorem activeLabels_eq_of_graph_period (o : GraphOutputs E) (v : Plane)
    (hv : Period (graph o) (v, (0 : V E))) (i : Channel p) (x : Plane) :
    activeLabels E o i (x + v) = activeLabels E o i x := by
  classical
  have hc : usefulAt E o i (x + v) = usefulAt E o i x := by
    funext w
    exact congrFun (graph_period_useful E o v hv x (Function.update 0 i w)) i
  ext j
  simp only [mem_activeLabels, Active, hc]

theorem selectedWord_period_of_graph_period (o : GraphOutputs E) (M : ℤ)
    (hv : Period (graph o) ((0, M), (0 : V E))) :
    VerticalPeriod (selectedWord E o) M := by
  intro n m
  have hs := activeLabels_eq_of_graph_period E o (0, M) hv (.inl n) (0, m)
  have hs' : activeLabels E o (.inl n) (0, m + M) =
      activeLabels E o (.inl n) (0, m) := by simpa only [Prod.mk_add_mk, zero_add] using hs
  exact congrArg selectSymbol hs'

theorem exists_positive_vertical_graph_period (o : GraphOutputs E)
    (hper : FullyPeriodic (graph o)) :
    ∃ M : ℕ, 0 < M ∧ Period (graph o) ((0, (M : ℤ)), (0 : V E)) := by
  obtain ⟨Λ, hΛ, hperiods⟩ := hper
  refine ⟨Λ.index, Nat.pos_of_ne_zero hΛ.index_ne_zero, ?_⟩
  have h := hperiods _ (Λ.nsmul_index_mem (((0, 1) : Plane), (0 : V E)))
  simpa only [Prod.smul_mk, smul_zero, nsmul_eq_mul, mul_one] using h

end PeriodicTilingThree

end

end OAI
