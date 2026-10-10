import Mathlib

namespace OAI

/-! Forced honeycomb walks and existence of their fixed-length free energy. -/

noncomputable section
open scoped ENNReal Topology
open Filter

namespace HoneycombForce

structure Vertex where
  col : ℤ
  row : ℤ
  up : Bool
  deriving DecidableEq

def up (i j : ℤ) : Vertex := ⟨i, j, true⟩
def down (i j : ℤ) : Vertex := ⟨i, j, false⟩

def UpDownAdj (v w : Vertex) : Prop :=
  v.up = true ∧ w.up = false ∧
    ((w.col = v.col ∧ w.row + 1 = v.row) ∨
     (w.col = v.col ∧ w.row = v.row) ∨
     (w.col + 1 = v.col ∧ w.row = v.row))

def Adj (v w : Vertex) : Prop := UpDownAdj v w ∨ UpDownAdj w v

def rowSpacing : ℝ := Real.sqrt 3 / 2

def position (v : Vertex) : ℂ :=
  if v.up then
    ⟨(v.col : ℝ) + (v.row : ℝ) / 2 + 1/2,
      rowSpacing * ((v.row : ℝ) + 1/3)⟩
  else
    ⟨(v.col : ℝ) + (v.row : ℝ) / 2 + 1,
      rowSpacing * ((v.row : ℝ) + 2/3)⟩

def rho : ℝ := (Real.sqrt (2 + Real.sqrt 2))⁻¹

def neighbors (v : Vertex) : Finset Vertex :=
  if v.up then
    {down v.col (v.row-1), down v.col v.row, down (v.col-1) v.row}
  else
    {up v.col (v.row+1), up v.col v.row, up (v.col+1) v.row}

def walkLists (o : Vertex) : ℕ → Finset (List Vertex)
  | 0 => {[o]}
  | n+1 => (neighbors o).biUnion (fun v => (walkLists v n).image (List.cons o))

def saws (o : Vertex) (n : ℕ) : Finset (List Vertex) :=
  (walkLists o n).filter List.Nodup

def endpoint (o : Vertex) (γ : List Vertex) : Vertex := γ.getLastD o

def displacement (o : Vertex) (γ : List Vertex) : ℂ :=
  position (endpoint o γ) - position o

def projection (e z : ℂ) : ℝ := (star e * z).re

def z (t : ℝ) : ℝ := rho * Real.exp (-t)

def green (o b : Vertex) (t : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ∑ γ ∈ saws o n,
    if endpoint o γ = b then ENNReal.ofReal (z t ^ n) else 0

def susceptibility (o : Vertex) (t : ℝ) : ℝ≥0∞ :=
  ∑' b : Vertex, green o b t

def directionalSum (o : Vertex) (e : ℂ) (t s : ℝ) : ℝ≥0∞ :=
  ∑' b : Vertex,
    ENNReal.ofReal (Real.exp (s * projection e (position b - position o))) * green o b t

def radialSum (o : Vertex) (t s : ℝ) : ℝ≥0∞ :=
  ∑' b : Vertex, ENNReal.ofReal (Real.exp (s * ‖position b - position o‖)) * green o b t

def directionalMass (o : Vertex) (e : ℂ) (t : ℝ) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ s : ℝ, 0 ≤ s ∧ r = ENNReal.ofReal s ∧
    directionalSum o e t s < ⊤}

def radialMass (o : Vertex) (t : ℝ) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ s : ℝ, 0 ≤ s ∧ r = ENNReal.ofReal s ∧
    radialSum o t s < ⊤}

def partition (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) : ℝ :=
  ∑ γ ∈ saws o n, rho ^ n * Real.exp (s * projection e (displacement o γ))

def logPartition (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) : ℝ :=
  Real.log (partition o e s n) / (n : ℝ)

def freeEnergy (o : Vertex) (e : ℂ) (s : ℝ) : ℝ :=
  Filter.limUnder atTop (logPartition o e s)

def PowerAtZero (a : ℝ → ℝ≥0∞) (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
    ENNReal.ofReal (t ^ (α + ε)) ≤ a t ∧ a t ≤ ENNReal.ofReal (t ^ (α - ε))

def UniformMassPowerAtZero (a : ℂ → ℝ → ℝ≥0∞) (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ e : ℂ, ‖e‖ = 1 → ∀ t : ℝ, 0 < t → t < δ →
      ENNReal.ofReal (t ^ (α + ε)) ≤ a e t ∧
      a e t ≤ ENNReal.ofReal (t ^ (α - ε))

def UniformRealPowerAtZero (a : ℂ → ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ e : ℂ, ‖e‖ = 1 → ∀ s : ℝ, 0 < s → s < δ →
      s ^ (α + ε) ≤ a e s ∧ a e s ≤ s ^ (α - ε)

theorem mem_neighbors_iff (v w : Vertex) : w ∈ neighbors v ↔ Adj v w := by
  rcases v with ⟨i, j, s⟩
  rcases w with ⟨k, l, t⟩
  cases s <;> cases t <;>
    simp [neighbors, Adj, UpDownAdj, up, down, Vertex.mk.injEq] <;> omega

theorem mem_walkLists_iff (o : Vertex) (n : ℕ) (γ : List Vertex) :
    γ ∈ walkLists o n ↔
      γ.head? = some o ∧ γ.length = n + 1 ∧ γ.IsChain Adj := by
  induction n generalizing o γ with
  | zero =>
      cases γ with
      | nil => simp [walkLists]
      | cons v vs =>
          cases vs with
          | nil => simp [walkLists, eq_comm]
          | cons w ws => simp [walkLists]
  | succ n ih =>
      simp only [walkLists, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨v, hv, xs, hxs, rfl⟩
        obtain ⟨hh, hl, hc⟩ := (ih v xs).mp hxs
        cases xs with
        | nil => simp at hh
        | cons w ws =>
            simp only [List.head?_cons, Option.some.injEq] at hh
            subst w
            exact ⟨rfl, by simpa using congrArg Nat.succ hl,
              List.isChain_cons_cons.mpr ⟨(mem_neighbors_iff o v).mp hv, hc⟩⟩
      · rintro ⟨hh, hl, hc⟩
        cases γ with
        | nil => simp at hh
        | cons v vs =>
            simp only [List.head?_cons, Option.some.injEq] at hh
            subst v
            cases vs with
            | nil => simp at hl
            | cons w ws =>
                obtain ⟨how, hws⟩ := List.isChain_cons_cons.mp hc
                refine ⟨w, (mem_neighbors_iff o w).mpr how, w :: ws, ?_, rfl⟩
                apply (ih w (w :: ws)).mpr
                exact ⟨rfl, by simpa using Nat.succ.inj hl, hws⟩

theorem mem_saws_iff (o : Vertex) (n : ℕ) (γ : List Vertex) :
    γ ∈ saws o n ↔ γ.head? = some o ∧ γ.length = n + 1 ∧
      γ.IsChain Adj ∧ γ.Nodup := by
  simp only [saws, Finset.mem_filter, mem_walkLists_iff]
  tauto

@[simp] theorem saws_zero (o : Vertex) : saws o 0 = {[o]} := by
  simp [saws, walkLists]

theorem rho_pos : 0 < rho := by
  unfold rho
  positivity

theorem rho_nonneg : 0 ≤ rho := rho_pos.le

theorem z_pos (t : ℝ) : 0 < z t := mul_pos rho_pos (Real.exp_pos _)

theorem partition_nonneg (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) :
    0 ≤ partition o e s n := by
  apply Finset.sum_nonneg
  intro γ _
  exact mul_nonneg (pow_nonneg rho_nonneg _) (Real.exp_pos _).le

@[simp] theorem partition_zero (o : Vertex) (e : ℂ) (s : ℝ) :
    partition o e s 0 = 1 := by
  simp [partition, endpoint, displacement, projection]

theorem projection_le_norm {e : ℂ} (he : ‖e‖ = 1) (v : ℂ) :
    projection e v ≤ ‖v‖ := by
  calc
    projection e v ≤ ‖star e * v‖ := Complex.re_le_norm _
    _ = ‖v‖ := by simp [he]

theorem directionalSum_le_radialSum (o : Vertex) {e : ℂ} (he : ‖e‖ = 1)
    (t : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    directionalSum o e t s ≤ radialSum o t s := by
  apply ENNReal.tsum_le_tsum
  intro b
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (projection_le_norm he _) hs

theorem radialMass_le_directionalMass (o : Vertex) {e : ℂ} (he : ‖e‖ = 1)
    (t : ℝ) : radialMass o t ≤ directionalMass o e t := by
  apply sSup_le_sSup
  rintro r ⟨s, hs, rfl, hfin⟩
  exact ⟨s, hs, rfl, lt_of_le_of_lt (directionalSum_le_radialSum o he t hs) hfin⟩

@[simp] theorem directionalSum_zero (o : Vertex) (e : ℂ) (t : ℝ) :
    directionalSum o e t 0 = susceptibility o t := by
  simp [directionalSum, susceptibility]

@[simp] theorem radialSum_zero (o : Vertex) (t : ℝ) :
    radialSum o t 0 = susceptibility o t := by
  simp [radialSum, susceptibility]

theorem radialSum_mono (o : Vertex) (t : ℝ) : Monotone (radialSum o t) := by
  intro s u hsu
  apply ENNReal.tsum_le_tsum
  intro b
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsu (norm_nonneg _))

def shiftVertex (i j : ℤ) (v : Vertex) : Vertex :=
  ⟨v.col + i, v.row + j, v.up⟩

theorem shiftVertex_injective (i j : ℤ) : Function.Injective (shiftVertex i j) := by
  intro v w h
  have hc := congrArg Vertex.col h
  have hr := congrArg Vertex.row h
  have hu := congrArg Vertex.up h
  cases v; cases w
  simp only [shiftVertex, Vertex.mk.injEq] at hc hr hu ⊢
  exact ⟨add_right_cancel hc, add_right_cancel hr, hu⟩

@[simp] theorem shiftVertex_adj (i j : ℤ) (v w : Vertex) :
    Adj (shiftVertex i j v) (shiftVertex i j w) ↔ Adj v w := by
  simp only [Adj, UpDownAdj, shiftVertex]
  constructor <;> intro h <;> rcases h with ⟨hv, hw, h⟩ | ⟨hw, hv, h⟩
  · left; refine ⟨hv, hw, ?_⟩; omega
  · right; refine ⟨hw, hv, ?_⟩; omega
  · left; refine ⟨hv, hw, ?_⟩; omega
  · right; refine ⟨hw, hv, ?_⟩; omega

def rowVertex (k : ℕ) : Vertex :=
  if k % 2 = 0 then up ((k / 2 : ℕ) : ℤ) 0 else down ((k / 2 : ℕ) : ℤ) 0

theorem rowVertex_injective : Function.Injective rowVertex := by
  intro k l h
  have hc := congrArg Vertex.col h
  have hs := congrArg Vertex.up h
  by_cases hk : k % 2 = 0 <;> by_cases hl : l % 2 = 0 <;>
    simp [rowVertex, hk, hl, up, down] at hc hs <;> omega

theorem rowVertex_adj (k : ℕ) : Adj (rowVertex k) (rowVertex (k+1)) := by
  by_cases hk : k % 2 = 0
  · have hk' : (k+1) % 2 ≠ 0 := by omega
    have he : (k+1) / 2 = k / 2 := by omega
    simp [rowVertex, hk, hk', Adj, UpDownAdj, up, down, he]
  · have hk' : (k+1) % 2 = 0 := by omega
    have he : (k+1) / 2 = k / 2 + 1 := by omega
    simp [rowVertex, hk, hk', Adj, UpDownAdj, up, down, he]

def ray (o : Vertex) (k : ℕ) : Vertex :=
  shiftVertex o.col o.row (rowVertex (k + if o.up then 0 else 1))

@[simp] theorem ray_zero (o : Vertex) : ray o 0 = o := by
  rcases o with ⟨i, j, u⟩
  cases u <;> simp [ray, rowVertex, shiftVertex, up, down]

theorem ray_injective (o : Vertex) : Function.Injective (ray o) :=
  (shiftVertex_injective _ _).comp (rowVertex_injective.comp
    (fun _ _ h => Nat.add_right_cancel h))

theorem ray_adj (o : Vertex) (k : ℕ) : Adj (ray o k) (ray o (k+1)) := by
  simp only [ray, shiftVertex_adj]
  rw [show k + 1 + (if o.up then 0 else 1) = (k + if o.up then 0 else 1) + 1 by omega]
  exact rowVertex_adj _

def rayPath (o : Vertex) (n : ℕ) : List Vertex :=
  List.ofFn (fun i : Fin (n+1) => ray o i.val)

theorem rayPath_mem (o : Vertex) (n : ℕ) : rayPath o n ∈ saws o n := by
  unfold rayPath
  apply (mem_saws_iff _ _ _).mpr
  refine ⟨?_, by simp, ?_, ?_⟩
  · rw [List.head?_eq_getElem?]
    simp
  · rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.getElem_ofFn]
    exact ray_adj o i
  · exact List.nodup_ofFn.mpr ((ray_injective o).comp Fin.val_injective)

theorem saws_nonempty (o : Vertex) (n : ℕ) : (saws o n).Nonempty :=
  ⟨rayPath o n, rayPath_mem o n⟩

theorem partition_pos (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) :
    0 < partition o e s n := by
  obtain ⟨γ, hγ⟩ := saws_nonempty o n
  apply lt_of_lt_of_le (mul_pos (pow_pos rho_pos n) (Real.exp_pos _))
  exact Finset.single_le_sum
    (fun γ _ => mul_nonneg (pow_nonneg rho_nonneg n) (Real.exp_pos _).le) hγ

private theorem ennreal_tsum_finsetSum {α β : Type*} (S : Finset β)
    (f : α → β → ℝ≥0∞) :
    (∑' a, ∑ b ∈ S, f a b) = ∑ b ∈ S, ∑' a, f a b := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert b S hb ih => simp [Finset.sum_insert, hb, ENNReal.tsum_add, ih]

theorem weighted_green_eq (o : Vertex) (t : ℝ) (R : Vertex → ℝ≥0∞) :
    (∑' b : Vertex, R b * green o b t) =
      ∑' n : ℕ, ∑ γ ∈ saws o n, R (endpoint o γ) * ENNReal.ofReal (z t ^ n) := by
  simp only [green, ← ENNReal.tsum_mul_left, Finset.mul_sum, mul_ite, mul_zero]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro n
  rw [ennreal_tsum_finsetSum]
  apply Finset.sum_congr rfl
  intro γ _
  rw [tsum_eq_single (endpoint o γ)]
  · simp
  · intro b hb
    simp [Ne.symm hb]

theorem z_pow (t : ℝ) (n : ℕ) :
    z t ^ n = rho ^ n * Real.exp (-t * (n : ℝ)) := by
  rw [z, mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

theorem directionalSum_eq (o : Vertex) (e : ℂ) (t s : ℝ) :
    directionalSum o e t s =
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-t * (n : ℝ)) * partition o e s n) := by
  rw [directionalSum, weighted_green_eq]
  apply tsum_congr
  intro n
  simp only [partition, Finset.mul_sum]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro γ _
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, z_pow]
    congr 1
    unfold displacement
    ring
  · intro γ _
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (pow_nonneg rho_nonneg _) (Real.exp_pos _).le)

theorem susceptibility_eq (o : Vertex) (t : ℝ) :
    susceptibility o t = ∑' n : ℕ,
      ENNReal.ofReal (Real.exp (-t * (n : ℝ)) * partition o 0 0 n) := by
  rw [← directionalSum_zero o 0 t, directionalSum_eq]

theorem directionalSum_finite_of_logPartition_limit (o : Vertex) (e : ℂ) (s : ℝ)
    {f t : ℝ} (hlim : Tendsto (logPartition o e s) atTop (𝓝 f)) (hft : f < t) :
    directionalSum o e t s < ⊤ := by
  rw [directionalSum_eq]
  apply Summable.tsum_ofReal_lt_top
  have hsum : Summable (fun n : ℕ => Real.exp ((n : ℝ) * ((f + t) / 2 - t))) :=
    Real.summable_exp_nat_mul_iff.mpr (by linarith)
  apply hsum.of_norm_bounded_eventually_nat
  have he := hlim.eventually (eventually_le_nhds (show f < (f + t) / 2 by linarith))
  filter_upwards [he, eventually_gt_atTop 0] with n hn hnpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlog : Real.log (partition o e s n) ≤ ((f + t) / 2) * (n : ℝ) :=
    (div_le_iff₀ hnR).mp hn
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (partition_nonneg o e s n))]
  calc
    Real.exp (-t * (n : ℝ)) * partition o e s n =
        Real.exp (-t * (n : ℝ) + Real.log (partition o e s n)) := by
      rw [Real.exp_add, Real.exp_log (partition_pos o e s n)]
    _ ≤ Real.exp ((n : ℝ) * ((f + t) / 2 - t)) := by
      apply Real.exp_le_exp.mpr
      nlinarith

theorem directionalSum_infinite_of_logPartition_limit (o : Vertex) (e : ℂ) (s : ℝ)
    {f t : ℝ} (hlim : Tendsto (logPartition o e s) atTop (𝓝 f)) (htf : t < f) :
    directionalSum o e t s = ⊤ := by
  rw [directionalSum_eq]
  by_contra hfin
  have hzero := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hfin
  suffices he : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (-t * (n : ℝ)) * partition o e s n) by
    have hbad : (1 : ℝ≥0∞) ≤ 0 := ge_of_tendsto hzero he
    exact not_le_of_gt zero_lt_one hbad
  have he := hlim.eventually (eventually_ge_nhds (show (t + f) / 2 < f by linarith))
  filter_upwards [he, eventually_gt_atTop 0] with n hn hnpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlog : ((t + f) / 2) * (n : ℝ) ≤ Real.log (partition o e s n) :=
    (le_div_iff₀ hnR).mp hn
  have hterm : 1 ≤ Real.exp (-t * (n : ℝ)) * partition o e s n := by
    rw [← Real.exp_log (partition_pos o e s n), ← Real.exp_add, Real.one_le_exp_iff]
    nlinarith
  simpa using ENNReal.ofReal_le_ofReal hterm

@[simp] theorem shiftVertex_shift (i j k l : ℤ) (v : Vertex) :
    shiftVertex i j (shiftVertex k l v) = shiftVertex (k+i) (l+j) v := by
  cases v
  simp [shiftVertex, add_assoc]

@[simp] theorem shiftVertex_zero (v : Vertex) : shiftVertex 0 0 v = v := by
  cases v
  simp [shiftVertex]

theorem position_shift (i j : ℤ) (v : Vertex) :
    position (shiftVertex i j v) = position v +
      (⟨(i : ℝ) + (j : ℝ) / 2, rowSpacing * (j : ℝ)⟩ : ℂ) := by
  rcases v with ⟨a, b, u⟩
  cases u <;> apply Complex.ext <;> simp [position, shiftVertex] <;> ring

theorem displacement_shift (i j : ℤ) (o : Vertex) (γ : List Vertex) :
    displacement (shiftVertex i j o) (γ.map (shiftVertex i j)) = displacement o γ := by
  unfold displacement endpoint
  rw [List.getLastD_map, position_shift, position_shift]
  abel

theorem mem_saws_shift {o : Vertex} {n : ℕ} {γ : List Vertex}
    (hγ : γ ∈ saws o n) (i j : ℤ) :
    γ.map (shiftVertex i j) ∈ saws (shiftVertex i j o) n := by
  obtain ⟨hh, hl, hc, hn⟩ := (mem_saws_iff _ _ _).mp hγ
  apply (mem_saws_iff _ _ _).mpr
  refine ⟨by simp [hh], by simpa using hl, ?_, ?_⟩
  · apply List.isChain_map_of_isChain _ _ hc
    intro v w hvw
    exact (shiftVertex_adj i j v w).mpr hvw
  · exact (List.nodup_map_iff (shiftVertex_injective i j)).mpr hn

theorem saws_shift (o : Vertex) (n : ℕ) (i j : ℤ) :
    saws (shiftVertex i j o) n = (saws o n).image (List.map (shiftVertex i j)) := by
  ext γ
  constructor
  · intro hγ
    refine Finset.mem_image.mpr ⟨γ.map (shiftVertex (-i) (-j)), ?_, ?_⟩
    · simpa using mem_saws_shift hγ (-i) (-j)
    · simp [List.map_map, Function.comp_def]
  · rintro hγ
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hγ
    exact mem_saws_shift hη i j

theorem partition_shift (o : Vertex) (n : ℕ) (i j : ℤ) (e : ℂ) (s : ℝ) :
    partition (shiftVertex i j o) e s n = partition o e s n := by
  unfold partition
  rw [saws_shift, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro γ _
    rw [displacement_shift]
  · exact fun _ _ _ _ h =>
      (List.map_injective_iff.mpr (shiftVertex_injective i j)) h

def baseVertex (u : Bool) : Vertex := ⟨0, 0, u⟩

theorem partition_eq_base (o : Vertex) (n : ℕ) (e : ℂ) (s : ℝ) :
    partition o e s n = partition (baseVertex o.up) e s n := by
  convert partition_shift (baseVertex o.up) n o.col o.row e s using 1
  cases o
  simp [baseVertex, shiftVertex]

def splitWalk (n : ℕ) (γ : List Vertex) : (Σ _ : List Vertex, List Vertex) :=
  ⟨γ.take (n+1), γ.drop n⟩

theorem splitWalk_injective (n : ℕ) : Function.Injective (splitWalk n) := by
  intro γ η h
  have hh := congrArg (fun p : (Σ _ : List Vertex, List Vertex) => p.1 ++ p.2.tail) h
  simpa [splitWalk, List.tail_drop, List.take_append_drop] using hh

theorem endpoint_take {o : Vertex} {γ : List Vertex} {n : ℕ} (hn : n < γ.length) :
    endpoint o (γ.take (n+1)) = γ[n] := by
  simp [endpoint, List.getLastD_eq_getLast?, List.getLast?_take, List.getElem?_eq_getElem hn]

theorem endpoint_drop {o p : Vertex} {γ : List Vertex} {n : ℕ} (hn : n < γ.length) :
    endpoint p (γ.drop n) = endpoint o γ := by
  have hγ : γ ≠ [] := by intro h; simp [h] at hn
  simp [endpoint, List.getLastD_eq_getLast?, List.getLast?_drop, hn.not_ge,
    List.getLast?_eq_some_getLast hγ]

theorem splitWalk_mem {o : Vertex} {n m : ℕ} {γ : List Vertex}
    (hγ : γ ∈ saws o (n+m)) :
    splitWalk n γ ∈ (saws o n).sigma (fun p => saws (endpoint o p) m) := by
  obtain ⟨hh, hl, hc, hnd⟩ := (mem_saws_iff _ _ _).mp hγ
  have hn : n < γ.length := by omega
  simp only [splitWalk, Finset.mem_sigma]
  constructor
  · apply (mem_saws_iff _ _ _).mpr
    refine ⟨?_, ?_, hc.take _, List.Pairwise.take hnd⟩
    · simpa [List.head?_take] using hh
    · simp only [List.length_take, hl]
      omega
  · apply (mem_saws_iff _ _ _).mpr
    refine ⟨?_, ?_, hc.drop _, List.Pairwise.drop hnd⟩
    · rw [endpoint_take hn]
      simp [List.getElem?_eq_getElem hn]
    · simp only [List.length_drop, hl]
      omega

theorem displacement_split {o : Vertex} {n m : ℕ} {γ : List Vertex}
    (hγ : γ ∈ saws o (n+m)) :
    displacement o γ = displacement o (γ.take (n+1)) +
      displacement (endpoint o (γ.take (n+1))) (γ.drop n) := by
  have hn : n < γ.length := by
    have hl := ((mem_saws_iff _ _ _).mp hγ).2.1
    omega
  unfold displacement
  rw [endpoint_drop hn]
  abel

theorem partition_split (o : Vertex) (e : ℂ) (s : ℝ) (n m : ℕ) :
    partition o e s (n+m) ≤ ∑ p ∈ saws o n,
      (rho ^ n * Real.exp (s * projection e (displacement o p))) *
        partition (endpoint o p) e s m := by
  let W : (Σ _ : List Vertex, List Vertex) → ℝ := fun p =>
    (rho ^ n * Real.exp (s * projection e (displacement o p.1))) *
      (rho ^ m * Real.exp (s * projection e (displacement (endpoint o p.1) p.2)))
  calc
    partition o e s (n+m) = ∑ γ ∈ saws o (n+m), W (splitWalk n γ) := by
      apply Finset.sum_congr rfl
      intro γ hγ
      dsimp [W, splitWalk]
      rw [displacement_split hγ, pow_add]
      simp only [projection, mul_add, Complex.add_re, Real.exp_add]
      ring
    _ = ∑ p ∈ (saws o (n+m)).image (splitWalk n), W p := by
      exact (Finset.sum_image (fun _ _ _ _ h => splitWalk_injective n h)).symm
    _ ≤ ∑ p ∈ (saws o n).sigma (fun p => saws (endpoint o p) m), W p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
        exact splitWalk_mem hγ
      · intro p _ _
        exact mul_nonneg
          (mul_nonneg (pow_nonneg rho_nonneg _) (Real.exp_pos _).le)
          (mul_nonneg (pow_nonneg rho_nonneg _) (Real.exp_pos _).le)
    _ = _ := by
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro p _
      simp [W, partition, Finset.mul_sum]

def maxPartition (e : ℂ) (s : ℝ) (n : ℕ) : ℝ :=
  max (partition (baseVertex true) e s n) (partition (baseVertex false) e s n)

theorem partition_le_maxPartition (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) :
    partition o e s n ≤ maxPartition e s n := by
  rw [partition_eq_base]
  cases o.up
  · exact le_max_right _ _
  · exact le_max_left _ _

theorem maxPartition_pos (e : ℂ) (s : ℝ) (n : ℕ) : 0 < maxPartition e s n :=
  (partition_pos (baseVertex true) e s n).trans_le (le_max_left _ _)

@[simp] theorem maxPartition_zero (e : ℂ) (s : ℝ) : maxPartition e s 0 = 1 := by
  simp [maxPartition]

theorem partition_le_mul_maxPartition (o : Vertex) (e : ℂ) (s : ℝ) (n m : ℕ) :
    partition o e s (n+m) ≤ partition o e s n * maxPartition e s m := by
  apply (partition_split o e s n m).trans
  rw [partition, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  exact mul_le_mul_of_nonneg_left (partition_le_maxPartition _ e s m)
    (mul_nonneg (pow_nonneg rho_nonneg _) (Real.exp_pos _).le)

theorem maxPartition_submultiplicative (e : ℂ) (s : ℝ) (n m : ℕ) :
    maxPartition e s (n+m) ≤ maxPartition e s n * maxPartition e s m := by
  apply max_le
  · exact (partition_le_mul_maxPartition _ e s n m).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (maxPartition_pos _ _ _).le)
  · exact (partition_le_mul_maxPartition _ e s n m).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (maxPartition_pos _ _ _).le)

theorem maxPartition_log_subadditive (e : ℂ) (s : ℝ) :
    Subadditive (fun n => Real.log (maxPartition e s n)) := by
  intro n m
  calc
    Real.log (maxPartition e s (n+m)) ≤
        Real.log (maxPartition e s n * maxPartition e s m) :=
      Real.log_le_log (maxPartition_pos _ _ _) (maxPartition_submultiplicative _ _ _ _)
    _ = _ := Real.log_mul (maxPartition_pos _ _ _).ne' (maxPartition_pos _ _ _).ne'

theorem endpoint_one_type {o : Vertex} {γ : List Vertex} (hγ : γ ∈ saws o 1) :
    (endpoint o γ).up = !o.up := by
  have hh := (Finset.mem_filter.mp hγ).1
  simp only [walkLists, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_singleton] at hh
  obtain ⟨v, hv, _, rfl, rfl⟩ := hh
  have hav := (mem_neighbors_iff o v).mp hv
  rcases hav with ⟨ho, hv, _⟩ | ⟨hv, ho, _⟩ <;> simp [endpoint, ho, hv]

theorem partition_succ_opposite (u : Bool) (e : ℂ) (s : ℝ) (n : ℕ) :
    partition (baseVertex u) e s (n+1) ≤
      partition (baseVertex u) e s 1 * partition (baseVertex (!u)) e s n := by
  rw [Nat.add_comm n 1]
  apply (partition_split (baseVertex u) e s 1 n).trans_eq
  conv_rhs => rw [partition, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [partition_eq_base (endpoint _ _), endpoint_one_type hγ]
  rfl

theorem maxPartition_succ_le (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) :
    maxPartition e s (n+1) ≤ maxPartition e s 1 * partition o e s n := by
  have same (u : Bool) : partition (baseVertex u) e s (n+1) ≤
      maxPartition e s 1 * partition (baseVertex u) e s n := by
    simpa only [mul_comm] using partition_le_mul_maxPartition (baseVertex u) e s n 1
  have opposite (u : Bool) : partition (baseVertex (!u)) e s (n+1) ≤
      maxPartition e s 1 * partition (baseVertex u) e s n := by
    simpa only [Bool.not_not] using (partition_succ_opposite (!u) e s n).trans
      (mul_le_mul_of_nonneg_right (partition_le_maxPartition _ e s 1)
        (partition_nonneg _ e s n))
  rw [partition_eq_base o]
  cases o.up
  · exact max_le (opposite false) (same false)
  · exact max_le (same true) (opposite true)

@[simp] theorem endpoint_rayPath (o : Vertex) (n : ℕ) :
    endpoint o (rayPath o n) = ray o n := by
  have hne : rayPath o n ≠ [] := by simp [rayPath]
  rw [endpoint, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
  simp only [Option.getD_some, rayPath, List.getLast_ofFn, Nat.add_sub_cancel]

theorem position_rowVertex (n : ℕ) :
    position (rowVertex n) - position (baseVertex true) =
      (⟨(n : ℝ) / 2, if n % 2 = 0 then 0 else rowSpacing / 3⟩ : ℂ) := by
  by_cases hn : n % 2 = 0
  · have hn' : (n / 2 : ℕ) * 2 = n := by omega
    have hr : ((n / 2 : ℕ) : ℝ) * 2 = n := by exact_mod_cast hn'
    apply Complex.ext <;> simp [rowVertex, hn, position, up, baseVertex, -Int.natCast_ediv]
    linarith
  · have hn' : (n / 2 : ℕ) * 2 + 1 = n := by omega
    have hr : ((n / 2 : ℕ) : ℝ) * 2 + 1 = n := by exact_mod_cast hn'
    apply Complex.ext <;> simp [rowVertex, hn, position, down, baseVertex, -Int.natCast_ediv] <;> linarith

def rowCost (e : ℂ) (s : ℝ) : ℝ :=
  |s * e.re / 2| + |s * e.im * rowSpacing / 3|

theorem rowPath_projection_lower (e : ℂ) (s : ℝ) {n : ℕ} (hn : 0 < n) :
    -(n : ℝ) * rowCost e s ≤
      s * projection e (displacement (baseVertex true) (rayPath (baseVertex true) n)) := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hx := mul_le_mul_of_nonneg_left (neg_abs_le (s * e.re / 2)) hn0
  have hy := neg_abs_le (s * e.im * rowSpacing / 3)
  have hy' := mul_le_mul_of_nonneg_right hnr (abs_nonneg (s * e.im * rowSpacing / 3))
  simp only [displacement, endpoint_rayPath, ray, baseVertex,
    ↓reduceIte, Nat.add_zero, shiftVertex_zero]
  rw [show (⟨0, 0, true⟩ : Vertex) = baseVertex true from rfl, position_rowVertex]
  by_cases hp : n % 2 = 0 <;>
    simp [projection, rowCost, hp, Complex.mul_re] <;>
    nlinarith [abs_nonneg (s * e.im * rowSpacing / 3)]

theorem maxPartition_log_linear_lower (e : ℂ) (s : ℝ) (n : ℕ) :
    (n : ℝ) * (Real.log rho - rowCost e s) ≤ Real.log (maxPartition e s n) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hw : rho ^ n * Real.exp (s * projection e
      (displacement (baseVertex true) (rayPath (baseVertex true) n))) ≤
      maxPartition e s n := by
    apply le_trans _ (partition_le_maxPartition (baseVertex true) e s n)
    unfold partition
    apply Finset.single_le_sum
      (f := fun γ => rho ^ n * Real.exp (s * projection e (displacement (baseVertex true) γ)))
      (a := rayPath (baseVertex true) n)
    · intro γ _
      exact mul_nonneg (pow_nonneg rho_nonneg _) (Real.exp_pos _).le
    · exact rayPath_mem (baseVertex true) n
  apply le_trans _ (Real.log_le_log (mul_pos (pow_pos rho_pos _) (Real.exp_pos _)) hw)
  rw [Real.log_mul (pow_pos rho_pos _).ne' (Real.exp_pos _).ne',
    Real.log_pow, Real.log_exp]
  have hp := rowPath_projection_lower e s (Nat.pos_of_ne_zero hn)
  linarith

theorem maxPartition_log_div_bddBelow (e : ℂ) (s : ℝ) :
    BddBelow (Set.range (fun n : ℕ => Real.log (maxPartition e s n) / (n : ℝ))) := by
  refine ⟨min 0 (Real.log rho - rowCost e s), ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : n = 0
  · subst n
    simp
  · apply (min_le_right _ _).trans
    apply (le_div_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
    simpa only [mul_comm] using maxPartition_log_linear_lower e s n

theorem exists_logPartition_limit (o : Vertex) (e : ℂ) (s : ℝ) :
    ∃ f : ℝ, Tendsto (logPartition o e s) atTop (𝓝 f) := by
  let hsub := maxPartition_log_subadditive e s
  have hlim := hsub.tendsto_lim (maxPartition_log_div_bddBelow e s)
  refine ⟨hsub.lim, ?_⟩
  have hshift := hlim.comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    simpa [Nat.cast_add, add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) 0 1 (d := 1) one_ne_zero)
  have hlower : Tendsto (fun n : ℕ =>
      (Real.log (maxPartition e s (n+1)) - Real.log (maxPartition e s 1)) / (n : ℝ))
      atTop (𝓝 hsub.lim) := by
    have h := (hshift.mul hratio).sub
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log (maxPartition e s 1)))
    simp only [mul_one, sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
    have hn1 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
    dsimp [Function.comp_def]
    field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hlim
  · filter_upwards with n
    have hlog := Real.log_le_log (maxPartition_pos e s (n+1))
      (maxPartition_succ_le o e s n)
    rw [Real.log_mul (maxPartition_pos e s 1).ne' (partition_pos o e s n).ne'] at hlog
    exact div_le_div_of_nonneg_right (by linarith :
      Real.log (maxPartition e s (n+1)) - Real.log (maxPartition e s 1) ≤
        Real.log (partition o e s n)) (Nat.cast_nonneg _)
  · filter_upwards with n
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (partition_pos o e s n) (partition_le_maxPartition o e s n))
      (Nat.cast_nonneg _)

theorem logPartition_tendsto (o : Vertex) (e : ℂ) (s : ℝ) :
    Tendsto (logPartition o e s) atTop (𝓝 (freeEnergy o e s)) :=
  tendsto_nhds_limUnder (exists_logPartition_limit o e s)

theorem directionalSum_finite_of_freeEnergy_lt (o : Vertex) (e : ℂ) (s : ℝ)
    {t : ℝ} (ht : freeEnergy o e s < t) : directionalSum o e t s < ⊤ :=
  directionalSum_finite_of_logPartition_limit o e s (logPartition_tendsto o e s) ht

theorem directionalSum_infinite_of_lt_freeEnergy (o : Vertex) (e : ℂ) (s : ℝ)
    {t : ℝ} (ht : t < freeEnergy o e s) : directionalSum o e t s = ⊤ :=
  directionalSum_infinite_of_logPartition_limit o e s (logPartition_tendsto o e s) ht

theorem directionalSum_le_susceptibility_add (o : Vertex) (e : ℂ) (t : ℝ)
    {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) :
    directionalSum o e t s ≤ susceptibility o t + directionalSum o e t u := by
  unfold directionalSum susceptibility
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro b
  let q := projection e (position b - position o)
  have hexp : Real.exp (s*q) ≤ 1 + Real.exp (u*q) := by
    by_cases hq : 0 ≤ q
    · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsu hq)).trans
        (le_add_of_nonneg_left zero_le_one)
    · have hsq : s*q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs (le_of_not_ge hq)
      exact (Real.exp_le_one_iff.mpr hsq).trans
        (le_add_of_nonneg_right (Real.exp_pos _).le)
  have h := ENNReal.ofReal_le_ofReal hexp
  rw [ENNReal.ofReal_add (by norm_num) (Real.exp_pos _).le, ENNReal.ofReal_one] at h
  change ENNReal.ofReal (Real.exp (s*q)) * green o b t ≤
    green o b t + ENNReal.ofReal (Real.exp (u*q)) * green o b t
  calc
    _ ≤ (1 + ENNReal.ofReal (Real.exp (u*q))) * green o b t := mul_le_mul_left h _
    _ = _ := by rw [add_mul, one_mul]

theorem directionalSum_finite_of_le (o : Vertex) (e : ℂ) {t s u : ℝ}
    (hχ : susceptibility o t < ⊤) (hu : directionalSum o e t u < ⊤)
    (hs : 0 ≤ s) (hsu : s ≤ u) : directionalSum o e t s < ⊤ :=
  (directionalSum_le_susceptibility_add o e t hs hsu).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hχ, hu⟩)

theorem freeEnergy_le_of_directionalSum_finite (o : Vertex) (e : ℂ) (s : ℝ)
    {t : ℝ} (ht : directionalSum o e t s < ⊤) : freeEnergy o e s ≤ t := by
  by_contra h
  have htop := directionalSum_infinite_of_lt_freeEnergy o e s (lt_of_not_ge h)
  rw [htop] at ht
  exact lt_irrefl _ ht

theorem freeEnergy_le_of_lt_mass (o : Vertex) (e : ℂ) {t s : ℝ}
    (hχ : susceptibility o t < ⊤) (hs : 0 ≤ s)
    (hm : ENNReal.ofReal s < directionalMass o e t) : freeEnergy o e s ≤ t := by
  obtain ⟨r, hr, hsr⟩ := lt_sSup_iff.mp hm
  obtain ⟨u, hu, rfl, hfin⟩ := hr
  have hsu : s < u := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs).mp hsr
  exact freeEnergy_le_of_directionalSum_finite o e s
    (directionalSum_finite_of_le o e hχ hfin hs hsu.le)

theorem freeEnergy_ge_of_mass_lt (o : Vertex) (e : ℂ) {t s : ℝ}
    (hs : 0 ≤ s) (hm : directionalMass o e t < ENNReal.ofReal s) :
    t ≤ freeEnergy o e s := by
  by_contra h
  have hfin := directionalSum_finite_of_freeEnergy_lt o e s (lt_of_not_ge h)
  have hle : ENNReal.ofReal s ≤ directionalMass o e t :=
    le_sSup ⟨s, hs, rfl, hfin⟩
  exact not_le_of_gt hm hle

theorem susceptibility_finite_of_radialMass_pos (o : Vertex) {t : ℝ}
    (h : 0 < radialMass o t) : susceptibility o t < ⊤ := by
  obtain ⟨r, hr, _⟩ := lt_sSup_iff.mp h
  obtain ⟨s, hs, rfl, hfin⟩ := hr
  have hle := radialSum_mono o t hs
  simpa using hle.trans_lt hfin

theorem freeEnergy_zero_le_of_radialMass_pos (o : Vertex) (e : ℂ) {t : ℝ}
    (h : 0 < radialMass o t) : freeEnergy o e 0 ≤ t := by
  apply freeEnergy_le_of_directionalSum_finite
  simpa using susceptibility_finite_of_radialMass_pos o h

theorem force_power_of_mass_powers (o : Vertex)
    (hm : UniformMassPowerAtZero (directionalMass o) (3/4 : ℝ))
    (hr : PowerAtZero (radialMass o) (3/4 : ℝ)) :
    UniformRealPowerAtZero (freeEnergy o) (4/3 : ℝ) := by
  intro ε hε
  let κ : ℝ := min ε (1/3)
  have hk : 0 < κ := lt_min hε (by norm_num)
  have hkε : κ ≤ ε := min_le_left _ _
  have hk1 : κ ≤ 1/3 := min_le_right _ _
  have hk2 : κ^2 ≤ κ/3 := by
    have := mul_nonneg hk.le (sub_nonneg.mpr hk1)
    nlinarith
  have hsmall : (4/3-κ) * (3/4+κ/16) < (1:ℝ) := by
    nlinarith [sq_nonneg κ]
  have hlarge : (1:ℝ) < (4/3+κ) * (3/4-κ/16) := by
    nlinarith
  obtain ⟨δm, hδm, Hm⟩ := hm (κ/16) (by positivity)
  obtain ⟨δr, hδr, Hr⟩ := hr 1 zero_lt_one
  have Hχ : ∀ t : ℝ, 0 < t → t < δr → susceptibility o t < ⊤ := by
    intro t ht htδ
    apply susceptibility_finite_of_radialMass_pos
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos ht _))
      (Hr t ht htδ).1
  refine ⟨min 1 (min δr δm), lt_min zero_lt_one (lt_min hδr hδm), ?_⟩
  intro e he s hs hsδ
  have hs1 : s < 1 := lt_of_lt_of_le hsδ (min_le_left _ _)
  have hsr : s < δr := lt_of_lt_of_le hsδ
    ((min_le_right _ _).trans (min_le_left _ _))
  have hsm : s < δm := lt_of_lt_of_le hsδ
    ((min_le_right _ _).trans (min_le_right _ _))
  have hqminus : s ^ ((4/3:ℝ)-κ) ≤ s := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hs hs1.le
      (show (1:ℝ) ≤ 4/3-κ by linarith)
  have hqplus : s ^ ((4/3:ℝ)+κ) ≤ s := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hs hs1.le
      (show (1:ℝ) ≤ 4/3+κ by linarith)
  have hs_lt : ENNReal.ofReal s <
      directionalMass o e (s ^ ((4/3:ℝ)-κ)) := by
    apply lt_of_lt_of_le _
      (Hm e he _ (Real.rpow_pos_of_pos hs _) (hqminus.trans_lt hsm)).1
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs.le).mpr
    rw [← Real.rpow_mul hs.le]
    simpa using Real.rpow_lt_rpow_of_exponent_gt hs hs1 hsmall
  have hm_lt : directionalMass o e (s ^ ((4/3:ℝ)+κ)) < ENNReal.ofReal s := by
    apply lt_of_le_of_lt
      (Hm e he _ (Real.rpow_pos_of_pos hs _) (hqplus.trans_lt hsm)).2
    apply (ENNReal.ofReal_lt_ofReal_iff hs).mpr
    rw [← Real.rpow_mul hs.le]
    simpa using Real.rpow_lt_rpow_of_exponent_gt hs hs1 hlarge
  constructor
  · exact (Real.rpow_le_rpow_of_exponent_ge hs hs1.le
      (show (4/3:ℝ)+κ ≤ 4/3+ε by linarith)).trans
        (freeEnergy_ge_of_mass_lt o e hs.le hm_lt)
  · exact (freeEnergy_le_of_lt_mass o e
      (Hχ _ (Real.rpow_pos_of_pos hs _) (hqminus.trans_lt hsr)) hs.le hs_lt).trans
      (Real.rpow_le_rpow_of_exponent_ge hs hs1.le
        (show (4/3:ℝ)-ε ≤ 4/3-κ by linarith))

theorem upDownAdj_sq_norm {v w : Vertex} (h : UpDownAdj v w) :
    ‖position w - position v‖ ^ 2 = (1/3 : ℝ) := by
  rcases v with ⟨i, j, u⟩
  rcases w with ⟨k, l, t⟩
  obtain ⟨hu, ht, h⟩ := h
  dsimp at hu ht h
  subst u; subst t
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [Complex.sq_norm, Complex.normSq_apply, position, Bool.false_eq_true,
      ite_false, ite_true, Complex.sub_re, Complex.sub_im,
      Int.cast_add, Int.cast_one, rowSpacing] <;>
    ring_nf <;> norm_num [Real.sq_sqrt]

theorem norm_adj_le_one {v w : Vertex} (h : Adj v w) :
    ‖position w - position v‖ ≤ 1 := by
  rcases h with h | h
  · have := upDownAdj_sq_norm h
    nlinarith [norm_nonneg (position w-position v)]
  · rw [norm_sub_rev]
    have := upDownAdj_sq_norm h
    nlinarith [norm_nonneg (position v-position w)]

theorem norm_displacement_one {o : Vertex} {γ : List Vertex} (h : γ ∈ saws o 1) :
    ‖displacement o γ‖ ≤ 1 := by
  obtain ⟨hh, hl, hc, _⟩ := (mem_saws_iff o 1 γ).mp h
  cases γ with
  | nil => simp at hh
  | cons a γ =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst a
    cases γ with
    | nil => simp at hl
    | cons b γ =>
      cases γ with
      | nil =>
        have hab : Adj o b := (List.isChain_cons_cons.mp hc).1
        simpa [displacement, endpoint] using norm_adj_le_one hab
      | cons c γ => simp at hl

theorem norm_displacement_le_length {o : Vertex} {n : ℕ} {γ : List Vertex}
    (h : γ ∈ saws o n) : ‖displacement o γ‖ ≤ (n : ℝ) := by
  induction n generalizing o γ with
  | zero =>
    simp only [saws_zero, Finset.mem_singleton] at h
    subst γ
    simp [displacement, endpoint]
  | succ n ih =>
    have hh : γ ∈ saws o (1+n) := by simpa [Nat.add_comm] using h
    have hp := splitWalk_mem hh
    simp only [splitWalk, Finset.mem_sigma] at hp
    rw [displacement_split hh]
    calc
      _ ≤ ‖displacement o (γ.take (1+1))‖ +
        ‖displacement (endpoint o (γ.take (1+1))) (γ.drop 1)‖ := norm_add_le _ _
      _ ≤ 1 + (n : ℝ) := add_le_add (norm_displacement_one hp.1) (ih hp.2)
      _ = (n+1 : ℕ) := by simp [add_comm]

theorem projection_abs_le_length {o : Vertex} {n : ℕ} {γ : List Vertex}
    (h : γ ∈ saws o n) {e : ℂ} (he : ‖e‖ = 1) :
    |projection e (displacement o γ)| ≤ (n : ℝ) := by
  calc
    _ ≤ ‖star e * displacement o γ‖ := Complex.abs_re_le_norm _
    _ = ‖displacement o γ‖ := by simp [he]
    _ ≤ (n : ℝ) := norm_displacement_le_length h

theorem partition_le_exp_mul (o : Vertex) {e : ℂ} (he : ‖e‖ = 1)
    (s u : ℝ) (n : ℕ) :
    partition o e s n ≤ Real.exp (|s-u| * (n:ℝ)) * partition o e u n := by
  unfold partition
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro γ hγ
  have hp : (s-u) * projection e (displacement o γ) ≤ |s-u| * (n:ℝ) := by
    calc
      _ ≤ |(s-u) * projection e (displacement o γ)| := le_abs_self _
      _ = |s-u| * |projection e (displacement o γ)| := abs_mul _ _
      _ ≤ |s-u| * (n:ℝ) := mul_le_mul_of_nonneg_left
        (projection_abs_le_length hγ he) (abs_nonneg _)
  calc
    _ ≤ rho^n * Real.exp (|s-u| * (n:ℝ) + u * projection e (displacement o γ)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg rho_nonneg _)
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = _ := by rw [Real.exp_add]; ring

theorem freeEnergy_le_add_abs (o : Vertex) {e : ℂ} (he : ‖e‖ = 1)
    (s u : ℝ) : freeEnergy o e s ≤ |s-u| + freeEnergy o e u := by
  apply le_of_tendsto_of_tendsto (logPartition_tendsto o e s)
    (tendsto_const_nhds.add (logPartition_tendsto o e u))
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlog := Real.log_le_log (partition_pos o e s n)
    (partition_le_exp_mul o he s u n)
  rw [Real.log_mul (Real.exp_pos _).ne' (partition_pos o e u n).ne', Real.log_exp] at hlog
  have hdiv := div_le_div_of_nonneg_right hlog hnR.le
  simpa [logPartition, add_div, hnR.ne'] using hdiv

theorem freeEnergy_zero_eq_of_mass_powers (o : Vertex)
    (hm : UniformMassPowerAtZero (directionalMass o) (3/4 : ℝ))
    (hr : PowerAtZero (radialMass o) (3/4 : ℝ))
    {e : ℂ} (he : ‖e‖ = 1) : freeEnergy o e 0 = 0 := by
  apply le_antisymm
  · by_contra hf
    have hfpos : 0 < freeEnergy o e 0 := lt_of_not_ge hf
    obtain ⟨δ, hδ, Hr⟩ := hr 1 zero_lt_one
    let t := min δ (freeEnergy o e 0) / 2
    have ht : 0 < t := half_pos (lt_min hδ hfpos)
    have htδ : t < δ := (half_lt_self (lt_min hδ hfpos)).trans_le
      (min_le_left _ _)
    have htf : t < freeEnergy o e 0 := (half_lt_self (lt_min hδ hfpos)).trans_le
      (min_le_right _ _)
    have hrpos : 0 < radialMass o t := lt_of_lt_of_le
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos ht _)) (Hr t ht htδ).1
    exact not_le_of_gt htf (freeEnergy_zero_le_of_radialMass_pos o e hrpos)
  · by_contra hf
    have hfneg : freeEnergy o e 0 < 0 := lt_of_not_ge hf
    obtain ⟨δ, hδ, Hf⟩ := force_power_of_mass_powers o hm hr 1 zero_lt_one
    let s := min δ (-freeEnergy o e 0) / 2
    have hs : 0 < s := half_pos (lt_min hδ (neg_pos.mpr hfneg))
    have hsδ : s < δ := (half_lt_self (lt_min hδ (neg_pos.mpr hfneg))).trans_le
      (min_le_left _ _)
    have hsf : s < -freeEnergy o e 0 :=
      (half_lt_self (lt_min hδ (neg_pos.mpr hfneg))).trans_le (min_le_right _ _)
    have hpos : 0 < freeEnergy o e s :=
      (Real.rpow_pos_of_pos hs _).trans_le (Hf e he s hs hsδ).1
    have hub := freeEnergy_le_add_abs o he s 0
    rw [sub_zero, abs_of_pos hs] at hub
    linarith

end HoneycombForce

end

end OAI
