import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.TimeRegularity

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def fullMixedD : MultiIndex → Field F → Field F
  | [], v => v
  | none :: a, v => fullTimeD (fullMixedD a v)
  | some i :: a, v => spaceD i (fullMixedD a v)

lemma JointSmooth.fullMixedD {v : Field F} (hv : JointSmooth v) (a : MultiIndex) :
    JointSmooth (fullMixedD a v) := by
  induction a with
  | nil => exact hv
  | cons i a ha =>
      cases i with
      | none => exact ha.fullTimeD
      | some i => exact ha.spaceD i

lemma JointSmooth.timeSlice {v : Field F} (hv : JointSmooth v) (x : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => v t x) := hv.comp (contDiff_id.prodMk contDiff_const)

lemma fullMixedD_eq_mixedD {v : Field F} (hv : JointSmooth v) (a : MultiIndex)
    (t : ℝ) (ht : 0 ≤ t) (x : Space) : fullMixedD a v t x = mixedD a v t x := by
  induction a generalizing t x with
  | nil => rfl
  | cons i a ha =>
    cases i with
    | none =>
      change deriv (fun s => fullMixedD a v s x) t =
        derivWithin (fun s => mixedD a v s x) (Ici 0) t
      rw [← derivWithin_congr (s := Ici (0 : ℝ)) (fun s hs => ha s hs x) (ha t ht x)]
      exact (((hv.fullMixedD a).timeSlice x).differentiable (by simp) t).derivWithin
        (uniqueDiffOn_Ici 0 t ht) |>.symm
    | some i =>
      change fderiv ℝ (fullMixedD a v t) x _ = fderiv ℝ (mixedD a v t) x _
      rw [show fullMixedD a v t = mixedD a v t from funext (ha t ht)]

def SpatiallySupported (K : Set Space) (v : Field F) : Prop :=
  ∀ t x, x ∉ K → v t x = 0

lemma SpatiallySupported.fullTimeD {K : Set Space} {v : Field F}
    (h : SpatiallySupported K v) : SpatiallySupported K (fullTimeD v) := by
  intro t x hx
  have he : (fun s => v s x) = fun _ => (0 : F) := funext (fun s => h s x hx)
  change deriv (fun s => v s x) t = 0
  rw [he]
  exact deriv_const t (0 : F)

lemma SpatiallySupported.spaceD {K : Set Space} {v : Field F}
    (h : SpatiallySupported K v) (hK : IsClosed K) (i : Fin 3) :
    SpatiallySupported K (spaceD i v) := by
  intro t x hx
  have he : v t =ᶠ[𝓝 x] 0 := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact h t y hy
  change fderiv ℝ (v t) x (Pi.single i 1) = 0
  rw [he.fderiv_eq]
  simp

lemma SpatiallySupported.fullMixedD {K : Set Space} {v : Field F}
    (h : SpatiallySupported K v) (hK : IsClosed K) (a : MultiIndex) :
    SpatiallySupported K (fullMixedD a v) := by
  induction a with
  | nil => exact h
  | cons i a ha =>
      cases i with
      | none => exact ha.fullTimeD
      | some i => exact ha.spaceD hK i

def RepeatsAfter (T : ℝ) (v : Field F) : Prop :=
  ∀ t, T ≤ t → v (t + 1) = v t

lemma RepeatsAfter.spaceD {T : ℝ} {v : Field F} (h : RepeatsAfter T v) (i : Fin 3) :
    RepeatsAfter T (spaceD i v) := by
  intro t ht
  funext x
  change fderiv ℝ (v (t + 1)) x (Pi.single i 1) = fderiv ℝ (v t) x (Pi.single i 1)
  rw [h t ht]

lemma RepeatsAfter.fullTimeD {T : ℝ} {v : Field F} (h : RepeatsAfter T v)
    (hv : JointSmooth v) : RepeatsAfter T (fullTimeD v) := by
  intro t ht
  funext x
  have hh := (hv.timeSlice x).differentiable (by simp)
  have hs : DifferentiableAt ℝ (fun s => v (s + 1) x) t :=
    (hh (t + 1)).comp t (differentiableAt_id.add_const 1)
  have he : EqOn (fun s => v (s + 1) x) (fun s => v s x) (Ici T) :=
    fun s hs => congrFun (h s hs) x
  change deriv (fun s => v s x) (t + 1) = deriv (fun s => v s x) t
  rw [← deriv_comp_add_const (fun s => v s x) 1 t,
    ← hs.derivWithin (uniqueDiffOn_Ici T t ht),
    derivWithin_congr he (he ht),
    (hh t).derivWithin (uniqueDiffOn_Ici T t ht)]

lemma RepeatsAfter.fullMixedD {T : ℝ} {v : Field F} (h : RepeatsAfter T v)
    (hv : JointSmooth v) (a : MultiIndex) : RepeatsAfter T (fullMixedD a v) := by
  induction a with
  | nil => exact h
  | cons i a ha =>
      cases i with
      | none => exact ha.fullTimeD (hv.fullMixedD a)
      | some i => exact ha.spaceD i

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
lemma RepeatsAfter.add_nat {T : ℝ} {v : Field F} (h : RepeatsAfter T v)
    {t : ℝ} (ht : T ≤ t) (n : ℕ) : v (t + n) = v t := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc, h _ (by linarith [Nat.cast_nonneg (α := ℝ) n]), ih]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
lemma RepeatsAfter.reduce {v : Field F} (h : RepeatsAfter 1 v) {t : ℝ} (ht : 0 ≤ t) :
    ∃ s ∈ Icc (0 : ℝ) 2, v t = v s := by
  by_cases ht' : t ≤ 2
  · exact ⟨t, ⟨ht, ht'⟩, rfl⟩
  · have htn : 0 ≤ t - 1 := by linarith
    let n := ⌊t - 1⌋₊
    have hle : (n : ℝ) ≤ t - 1 := Nat.floor_le htn
    have hlt : t - 1 < (n : ℝ) + 1 := Nat.lt_floor_add_one (t - 1)
    refine ⟨t - n, ⟨by linarith, by linarith⟩, ?_⟩
    have he := h.add_nat (t := t - n) (by linarith) n
    simpa using he

theorem boundedMixed_of_compact_repeating {K : Set Space} (hK : IsCompact K)
    {v : Field F} (hv : JointSmooth v) (hs : SpatiallySupported K v)
    (hp : RepeatsAfter 1 v) : BoundedMixed v := by
  intro a
  have ha := hv.fullMixedD a
  have hsa := hs.fullMixedD hK.isClosed a
  have hpa := hp.fullMixedD hv a
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    ha.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t ht x => ?_⟩
  rw [← fullMixedD_eq_mixedD hv a t ht x]
  obtain ⟨s, hs, he⟩ := hpa.reduce ht
  rw [congrFun he x]
  by_cases hx : x ∈ K
  · exact (hC (s, x) ⟨hs,hx⟩).trans (le_max_left _ _)
  · rw [hsa s x hx, norm_zero]
    exact le_max_right _ _

end BalancedTransport.Geometry
end

end OAI
