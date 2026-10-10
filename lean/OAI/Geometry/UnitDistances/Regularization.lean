import OAI.Geometry.UnitDistances.Powers

namespace OAI

namespace PlanarUnitDistances.IncidenceRegularization
open Finset Real

noncomputable def mass {A : Type*} (μ : A → ℝ) (s : Finset A) : ℝ := ∑ a ∈ s, μ a
noncomputable def rect {P Q : Type*} (w : P → Q → ℝ)
    (F : Finset P) (G : Finset Q) : ℝ := ∑ p ∈ F, ∑ q ∈ G, w p q

lemma mass_nonneg {A : Type*} (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (s : Finset A) :
    0 ≤ mass μ s := sum_nonneg (fun a _ => hμ a)
lemma mass_mono {A : Type*} (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    {s t : Finset A} (hst : s ⊆ t) : mass μ s ≤ mass μ t :=
  sum_le_sum_of_subset_of_nonneg hst (fun a _ _ => hμ a)
lemma rect_nonneg {P Q : Type*} (w : P → Q → ℝ) (hw : ∀ p q, 0 ≤ w p q)
    (F : Finset P) (G : Finset Q) : 0 ≤ rect w F G :=
  sum_nonneg (fun p _ => sum_nonneg (fun q _ => hw p q))

section Optimizer
variable {P Q : Type*} [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
variable (μ : P → ℝ) (ν : Q → ℝ) (w : P → Q → ℝ)

noncomputable def objective (γ : ℝ) (F : Finset P) (G : Finset Q) : ℝ :=
  rect w F G / (mass μ F * mass ν G)^γ

def IsMaximizing (τ γ : ℝ) (F : Finset P) (G : Finset Q) : Prop :=
  τ ≤ mass μ F ∧ τ ≤ mass ν G ∧
    ∀ A B, τ ≤ mass μ A → τ ≤ mass ν B →
      objective μ ν w γ A B ≤ objective μ ν w γ F G

omit [DecidableEq P] [DecidableEq Q] in

theorem exists_maximizing {τ γ : ℝ} (hτ : τ ≤ 1)
    (hμ : ∑ p, μ p = 1) (hν : ∑ q, ν q = 1)
    (hw : ∑ p, ∑ q, w p q = 1) :
    ∃ F G, IsMaximizing μ ν w τ γ F G ∧ 1 ≤ objective μ ν w γ F G := by
  classical
  let S : Finset (Finset P × Finset Q) := univ.filter fun x =>
    τ ≤ mass μ x.1 ∧ τ ≤ mass ν x.2
  have hfull : ((univ : Finset P), (univ : Finset Q)) ∈ S := by
    apply mem_filter.mpr
    exact ⟨mem_univ _, by simpa [mass,hμ,hν] using And.intro hτ hτ⟩
  obtain ⟨⟨F,G⟩,hFG,hmax⟩ := S.exists_max_image
    (fun x => objective μ ν w γ x.1 x.2) ⟨_,hfull⟩
  have hfeas := (mem_filter.mp hFG).2
  refine ⟨F,G,⟨hfeas.1,hfeas.2,?_⟩,?_⟩
  · intro A B hA hB
    exact hmax (A,B) (by simp [S,hA,hB])
  · have hh := hmax (univ,univ) hfull
    simpa [objective, mass, rect, hμ, hν, hw] using hh

omit [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q] in
lemma winner_positive {τ γ : ℝ} {F : Finset P} {G : Finset Q}
    (hτ : 0 < τ) (hmax : IsMaximizing μ ν w τ γ F G)
    (hwin : 1 ≤ objective μ ν w γ F G) :
    0 < mass μ F ∧ 0 < mass ν G ∧ 0 < rect w F G ∧
      (mass μ F * mass ν G)^γ ≤ rect w F G := by
  have hU := hτ.trans_le hmax.1
  have hV := hτ.trans_le hmax.2.1
  have hpow := rpow_pos_of_pos (mul_pos hU hV) γ
  have hW : (mass μ F * mass ν G)^γ ≤ rect w F G := by
    simpa using (le_div_iff₀ hpow).mp hwin
  exact ⟨hU,hV,hpow.trans_le hW,hW⟩

omit [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q] in

theorem feasible_expansion {τ γ : ℝ} {F : Finset P} {G : Finset Q}
    (hτ : 0 < τ) (hmax : IsMaximizing μ ν w τ γ F G)
    (hW : 0 < rect w F G) (A : Finset P) (B : Finset Q)
    (hA : τ ≤ mass μ A) (hB : τ ≤ mass ν B) :
    rect w A B / rect w F G ≤
      (mass μ A / mass μ F * (mass ν B / mass ν G))^γ := by
  have hU := hτ.trans_le hmax.1
  have hV := hτ.trans_le hmax.2.1
  have hα := hτ.trans_le hA
  have hβ := hτ.trans_le hB
  have hUV := rpow_pos_of_pos (mul_pos hU hV) γ
  have hαβ := rpow_pos_of_pos (mul_pos hα hβ) γ
  have ho := hmax.2.2 A B hA hB
  unfold objective at ho
  have ho' := (div_le_div_iff₀ hαβ hUV).mp ho
  have hid : mass μ A / mass μ F * (mass ν B / mass ν G) =
      (mass μ A * mass ν B)/(mass μ F * mass ν G) := by ring
  rw [hid, div_rpow (mul_pos hα hβ).le (mul_pos hU hV).le]
  exact (div_le_div_iff₀ hW hUV).mpr (by nlinarith)

omit [Fintype P] [Fintype Q] [DecidableEq Q] in

theorem left_atom_bound {τ γ : ℝ} (_hμ : ∀ p, 0 ≤ μ p)
    {F : Finset P} {G : Finset Q} (hτ : 0 < τ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hmax : IsMaximizing μ ν w τ γ F G) (hW : 0 < rect w F G)
    {p : P} (hp : p ∈ F) (herase : τ ≤ mass μ (F.erase p)) :
    γ * (μ p / mass μ F) ≤ (∑ q ∈ G, w p q) / rect w F G := by
  have hU := hτ.trans_le hmax.1
  have hV := hτ.trans_le hmax.2.1
  have hsum : mass μ (F.erase p) + μ p = mass μ F := by
    exact sum_erase_add _ _ hp
  have hrect : rect w (F.erase p) G + (∑ q ∈ G, w p q) = rect w F G := by
    exact sum_erase_add _ _ hp
  have he := feasible_expansion μ ν w hτ hmax hW (F.erase p) G herase hmax.2.1
  have hratio : mass μ (F.erase p) / mass μ F = 1 - μ p / mass μ F := by
    apply (div_eq_iff hU.ne').mpr
    field_simp
    linarith
  rw [div_self hV.ne', mul_one, hratio] at he
  have hple : μ p ≤ mass μ F := by linarith [mass_nonneg μ _hμ (F.erase p)]
  have hratio1 : μ p / mass μ F ≤ 1 := (div_le_one hU).mpr hple
  have hBern := rpow_one_add_le_one_add_mul_self
    (by linarith : -1 ≤ -(μ p / mass μ F)) hγ hγ1
  have hBern' : (1 - μ p / mass μ F)^γ ≤ 1-γ*(μ p / mass μ F) := by
    convert hBern using 1; ring
  have he' := he.trans hBern'
  have hd : rect w (F.erase p) G / rect w F G +
      (∑ q ∈ G, w p q) / rect w F G = 1 := by
    rw [← add_div, hrect, div_self hW.ne']
  linarith

omit [DecidableEq P] in
lemma mass_le_one (hμ : ∀ p, 0 ≤ μ p) (hs : ∑ p, μ p = 1) (F : Finset P) :
    mass μ F ≤ 1 := by
  simpa [mass,hs] using mass_mono μ hμ (subset_univ F)

omit [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q] in
lemma transpose_maximizing {τ γ : ℝ} {F : Finset P} {G : Finset Q}
    (hm : IsMaximizing μ ν w τ γ F G) :
    IsMaximizing ν μ (fun q p => w p q) τ γ G F := by
  refine ⟨hm.2.1,hm.1,?_⟩
  intro B A hB hA
  have hh := hm.2.2 A B hA hB
  have hrect (A : Finset P) (B : Finset Q) :
      rect (fun q p => w p q) B A = rect w A B := sum_comm
  simpa only [objective, hrect, mul_comm] using hh

omit [Fintype P] [Fintype Q] [DecidableEq P] in
theorem right_atom_bound {τ γ : ℝ} (hν : ∀ q, 0 ≤ ν q)
    {F : Finset P} {G : Finset Q} (hτ : 0 < τ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hmax : IsMaximizing μ ν w τ γ F G) (hW : 0 < rect w F G)
    {q : Q} (hq : q ∈ G) (herase : τ ≤ mass ν (G.erase q)) :
    γ * (ν q / mass ν G) ≤ (∑ p ∈ F, w p q) / rect w F G := by
  have ht : rect (fun q p => w p q) G F = rect w F G := sum_comm
  have he := left_atom_bound ν μ (fun q p => w p q) hν hτ hγ hγ1
    (transpose_maximizing μ ν w hmax) (by rw [ht]; exact hW) hq herase
  simpa only [ht] using he

end Optimizer

lemma min_le_geometric {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min x y ≤ sqrt (x*y) := by
  have hh : (min x y)^2 ≤ x*y := by
    rcases le_total x y with h|h
    · rw [min_eq_left h]
      nlinarith [mul_nonneg hx (sub_nonneg.mpr h)]
    · rw [min_eq_right h]
      nlinarith [mul_nonneg hy (sub_nonneg.mpr h)]
  have hs := sq_sqrt (mul_nonneg hx hy)
  have hn := sqrt_nonneg (x*y)
  nlinarith [min_le_left x y, min_le_right x y]

theorem preliminary_square_root {u v a b T w : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 ≤ T)
    (hi : w ≤ T*((u*v)^((2:ℝ)/3)+a*v+b*u))
    (hdP : w ≤ T*u) (hdQ : w ≤ T*v) :
    w ≤ T*sqrt (u*v)*((u*v)^((1:ℝ)/6)+sqrt a+sqrt b) := by
  have hA := rpow_nonneg (mul_nonneg hu hv) ((2:ℝ)/3)
  have hc : w ≤ T*((u*v)^((2:ℝ)/3)+min (a*v) u+min (b*u) v) := by
    by_cases h1 : a*v ≤ u
    · rw [min_eq_left h1]
      by_cases h2 : b*u ≤ v
      · simpa only [min_eq_left h2] using hi
      · rw [min_eq_right (le_of_not_ge h2)]
        exact hdQ.trans (mul_le_mul_of_nonneg_left (by nlinarith) hT)
    · rw [min_eq_right (le_of_not_ge h1)]
      exact hdP.trans (mul_le_mul_of_nonneg_left
        (by linarith [le_min (mul_nonneg hb hu) hv]) hT)
  have hz1 : min (a*v) u ≤ sqrt a * sqrt (u*v) := by
    have := min_le_geometric (mul_nonneg ha hv) hu
    convert this using 1
    rw [← sqrt_mul ha]
    congr 1
    ring
  have hz2 : min (b*u) v ≤ sqrt b * sqrt (u*v) := by
    have := min_le_geometric (mul_nonneg hb hu) hv
    convert this using 1
    rw [← sqrt_mul hb]
    congr 1
    ring
  have hpow : (u*v)^((2:ℝ)/3) = sqrt (u*v)*(u*v)^((1:ℝ)/6) := by
    by_cases hzero : u*v = 0
    · simp [hzero, zero_rpow (by norm_num : (2:ℝ)/3 ≠ 0)]
    · rw [sqrt_eq_rpow, ← rpow_add (lt_of_le_of_ne (mul_nonneg hu hv) (Ne.symm hzero))]
      norm_num
  calc
    w ≤ T*((u*v)^((2:ℝ)/3)+min (a*v) u+min (b*u) v) := hc
    _ ≤ T*((u*v)^((2:ℝ)/3)+sqrt a*sqrt (u*v)+sqrt b*sqrt (u*v)) :=
      mul_le_mul_of_nonneg_left (by linarith) hT
    _ = T*sqrt (u*v)*((u*v)^((1:ℝ)/6)+sqrt a+sqrt b) := by rw [hpow]; ring

lemma renormalized_preliminary {α β U V W T ρ e x : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hU : 0 < U) (hV : 0 < V)
    (hU1 : U ≤ 1) (hV1 : V ≤ 1) (hW : 0 < W)
    (hT : 0 ≤ T) (hρ : 0 ≤ ρ)
    (hp : x ≤ T*sqrt (α*β)*((α*β)^ρ+e)) :
    x/W ≤ (T*sqrt (U*V)/W)*sqrt (α/U*(β/V))*
      ((α/U*(β/V))^ρ+e) := by
  have hUV : 0 < U*V := mul_pos hU hV
  have huv : 0 ≤ α/U*(β/V) := mul_nonneg (div_nonneg hα hU.le) (div_nonneg hβ hV.le)
  have hid : α*β = (U*V)*(α/U*(β/V)) := by field_simp
  have hUV1 : U*V ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hU1) (sub_nonneg.mpr hV1)]
  have hle : α*β ≤ α/U*(β/V) := by rw [hid]; nlinarith
  have hr := rpow_le_rpow (mul_nonneg hα hβ) hle hρ
  have hrt : 0 ≤ T*sqrt (α*β) := mul_nonneg hT (sqrt_nonneg _)
  have hb := hp.trans (mul_le_mul_of_nonneg_left (show (α*β)^ρ+e ≤ (α/U*(β/V))^ρ+e by linarith) hrt)
  have hs : sqrt (α*β) = sqrt (U*V)*sqrt (α/U*(β/V)) := by
    rw [hid, sqrt_mul hUV.le]
  apply (div_le_iff₀ hW).mpr
  have heq : (T*sqrt (U*V)/W)*sqrt (α/U*(β/V))*
      ((α/U*(β/V))^ρ+e)*W = T*(sqrt (U*V)*sqrt (α/U*(β/V)))*
      ((α/U*(β/V))^ρ+e) := by field_simp
  rw [heq]
  simpa [hs] using hb

theorem maximizing_expansion {P Q : Type*} [Fintype P] [Fintype Q]
    [DecidableEq P] [DecidableEq Q]
    (μ : P → ℝ) (ν : Q → ℝ) (w : P → Q → ℝ)
    (hμ : ∀ p, 0 ≤ μ p) (hν : ∀ q, 0 ≤ ν q)
    (hμs : ∑ p, μ p = 1) (hνs : ∑ q, ν q = 1)
    {τ η ρ T e : ℝ} (hτ : 0 < τ) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hT : 0 ≤ T) (he : 0 ≤ e)
    {F : Finset P} {G : Finset Q}
    (hm : IsMaximizing μ ν w τ ((1:ℝ)/2+η) F G)
    (hW : 0 < rect w F G)
    (hpre : ∀ A B, rect w A B ≤
      T*sqrt (mass μ A * mass ν B)*((mass μ A * mass ν B)^ρ+e)) :
    let ξ := (T*sqrt (mass μ F * mass ν G)/rect w F G)*
      ((τ/min (mass μ F) (mass ν G))^ρ+e)
    ∀ A ⊆ F, ∀ B ⊆ G,
      rect w A B/rect w F G ≤
        sqrt (mass μ A/mass μ F*(mass ν B/mass ν G))*
          ((mass μ A/mass μ F*(mass ν B/mass ν G))^η+ξ) := by
  dsimp only
  intro A hAF B hBG
  let U := mass μ F
  let V := mass ν G
  let α := mass μ A
  let β := mass ν B
  let W := rect w F G
  let u := α/U
  let v := β/V
  let C := T*sqrt (U*V)/W
  let ξ := C*((τ/min U V)^ρ+e)
  have hU : 0 < U := hτ.trans_le hm.1
  have hV : 0 < V := hτ.trans_le hm.2.1
  have hU1 : U ≤ 1 := mass_le_one μ hμ hμs F
  have hV1 : V ≤ 1 := mass_le_one ν hν hνs G
  have hα : 0 ≤ α := mass_nonneg μ hμ A
  have hβ : 0 ≤ β := mass_nonneg ν hν B
  have hαU : α ≤ U := mass_mono μ hμ hAF
  have hβV : β ≤ V := mass_mono ν hν hBG
  have hu : 0 ≤ u := div_nonneg hα hU.le
  have hv : 0 ≤ v := div_nonneg hβ hV.le
  have hu1 : u ≤ 1 := (div_le_one hU).mpr hαU
  have hv1 : v ≤ 1 := (div_le_one hV).mpr hβV
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hT (sqrt_nonneg _)) hW.le
  have hmin : 0 < min U V := lt_min hU hV
  have hξ : 0 ≤ ξ := mul_nonneg hC (add_nonneg (rpow_nonneg
    (div_nonneg hτ.le hmin.le) ρ) he)
  have hsplit : (u*v)^((1:ℝ)/2+η) = sqrt (u*v)*(u*v)^η := by
    rw [sqrt_eq_rpow, ← rpow_add' (mul_nonneg hu hv) (by linarith : (1:ℝ)/2+η ≠ 0)]
  change rect w A B/W ≤ sqrt (u*v)*((u*v)^η+ξ)
  by_cases hfeas : τ ≤ α ∧ τ ≤ β
  · have hh := feasible_expansion μ ν w hτ hm hW A B hfeas.1 hfeas.2
    change rect w A B/W ≤ (u*v)^((1:ℝ)/2+η) at hh
    rw [hsplit] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith) (sqrt_nonneg _))
  · have hsmall : u*v ≤ τ/min U V := by
      by_cases ha : τ ≤ α
      · have hb : β < τ := lt_of_not_ge (fun hb => hfeas ⟨ha,hb⟩)
        have hvτ : v ≤ τ/V := (div_le_div_iff_of_pos_right hV).mpr hb.le
        have hτm : τ/V ≤ τ/min U V := div_le_div_of_nonneg_left hτ.le hmin (min_le_right _ _)
        have huv : u*v ≤ v := by nlinarith
        exact huv.trans (hvτ.trans hτm)
      · have hατ : α < τ := lt_of_not_ge ha
        have huτ : u ≤ τ/U := (div_le_div_iff_of_pos_right hU).mpr hατ.le
        have hτm : τ/U ≤ τ/min U V := div_le_div_of_nonneg_left hτ.le hmin (min_le_left _ _)
        have huv : u*v ≤ u := by nlinarith
        exact huv.trans (huτ.trans hτm)
    have hp := renormalized_preliminary hα hβ hU hV hU1 hV1 hW hT hρ (hpre A B)
    change rect w A B/W ≤ C*sqrt (u*v)*((u*v)^ρ+e) at hp
    have hr := rpow_le_rpow (mul_nonneg hu hv) hsmall hρ
    calc
      rect w A B/W ≤ C*sqrt (u*v)*((u*v)^ρ+e) := hp
      _ ≤ C*sqrt (u*v)*((τ/min U V)^ρ+e) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC (sqrt_nonneg _))
      _ = sqrt (u*v)*ξ := by dsimp [ξ]; ring
      _ ≤ sqrt (u*v)*((u*v)^η+ξ) :=
        mul_le_mul_of_nonneg_left (by linarith [rpow_nonneg (mul_nonneg hu hv) η]) (sqrt_nonneg _)

end PlanarUnitDistances.IncidenceRegularization

namespace PlanarUnitDistances.GeometricExpansion
open CircleIncidence CircleCutting IncidenceRegularization
open scoped Classical
noncomputable section

def factor (m n e L dP dQ t a : ℝ) : ℝ :=
  1+1000*L^2*(m*n)^(2/3:ℝ)/e+1000*L^2*n*t^a/e+
    1000*L^2*m*t/e+dP*m/e+dQ*n/e

lemma factor_bounds {m n e L dP dQ t a : ℝ}
    (hm : 0≤ m) (hn : 0≤ n) (he : 0< e) (hdP : 0≤ dP) (hdQ : 0≤ dQ) (ht : 0< t) :
    1≤ factor m n e L dP dQ t a ∧
    1000*L^2*(m*n)^(2/3:ℝ)/e≤ factor m n e L dP dQ t a ∧
    1000*L^2*n*t^a/e≤ factor m n e L dP dQ t a ∧
    1000*L^2*m*t/e≤ factor m n e L dP dQ t a ∧
    dP*m/e≤ factor m n e L dP dQ t a ∧
    dQ*n/e≤ factor m n e L dP dQ t a := by
  have h1 : 0≤ 1000*L^2*(m*n)^(2/3:ℝ)/e := by positivity
  have h2 : 0≤ 1000*L^2*n*t^a/e := by positivity
  have h3 : 0≤ 1000*L^2*m*t/e := by positivity
  have h4 : 0≤ dP*m/e := by positivity
  have h5 : 0≤ dQ*n/e := by positivity
  unfold factor
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma incidence_degree_le (P Q : Finset Plane) {D : ℝ} (hD : ∀p∈P,degree Q p≤ D) :
    incidences P Q≤(P.card:ℝ)*D := by
  rw [incidences_comm]
  unfold incidences
  exact (Finset.sum_le_sum hD).trans_eq (by simp)

theorem preliminary (P Q : Finset Plane) {L dP dQ t a : ℝ}
    (hE : 0< incidences P Q) (hL : 1≤ L)
    (hlP : cuttingLog P.card≤ L) (hlQ : cuttingLog Q.card≤ L)
    (hdP : 0≤ dP) (hdQ : 0≤ dQ) (ht : 0< t)
    (hP : ∀p∈P,degree Q p≤ dP) (hQ : ∀q∈Q,degree P q≤ dQ) :
    ∀F⊆P,∀G⊆Q,
      let u := (F.card:ℝ)/(P.card:ℝ)
      let v := (G.card:ℝ)/(Q.card:ℝ)
      let T := factor (P.card:ℝ) (Q.card:ℝ) (incidences P Q) L dP dQ t a
      incidences F G/incidences P Q ≤
        T*Real.sqrt (u*v)*((u*v)^(1/6:ℝ)+Real.sqrt (t^(-a))+Real.sqrt (t^(-1:ℝ))) := by
  intro F hF G hG
  dsimp only
  let m : ℝ := P.card
  let n : ℝ := Q.card
  let e := incidences P Q
  let u : ℝ := (F.card:ℝ)/m
  let v : ℝ := (G.card:ℝ)/n
  let T := factor m n e L dP dQ t a
  have hm0 : 0≤ m := Nat.cast_nonneg _
  have hn0 : 0≤ n := Nat.cast_nonneg _
  have hmn : 0< m*n := hE.trans_le (incidences_le P Q)
  have hm : 0< m := pos_of_mul_pos_left hmn hn0
  have hn : 0< n := pos_of_mul_pos_right hmn hm0
  have hu : 0≤ u := div_nonneg (Nat.cast_nonneg _) hm0
  have hv : 0≤ v := div_nonneg (Nat.cast_nonneg _) hn0
  have hT := factor_bounds hm0 hn0 hE hdP hdQ ht (a:=a) (L:=L)
  have hcF : (F.card:ℝ)=m*u := by
    dsimp only [u]
    calc
      _ = (F.card:ℝ)*(m/m) := by rw [div_self hm.ne',mul_one]
      _ = m*((F.card:ℝ)/m) := by ring
  have hcG : (G.card:ℝ)=n*v := by
    dsimp only [v]
    calc
      _ = (G.card:ℝ)*(n/n) := by rw [div_self hn.ne',mul_one]
      _ = n*((G.card:ℝ)/n) := by ring
  have hraw := incidence_bound_enlarged F G hL
    ((cuttingLog_mono (Finset.card_le_card hF)).trans hlP)
    ((cuttingLog_mono (Finset.card_le_card hG)).trans hlQ) le_rfl le_rfl
  have hmul : ((F.card:ℝ)*G.card)^(2/3:ℝ)=(m*n)^(2/3:ℝ)*(u*v)^(2/3:ℝ) := by
    rw [hcF,hcG]
    have heq : m*u*(n*v)=(m*n)*(u*v) := by ring
    rw [heq,Real.mul_rpow (mul_nonneg hm0 hn0) (mul_nonneg hu hv)]
  have htcan : t^a*t^(-a)=1 := by rw [←Real.rpow_add ht]; simp
  have htcan1 : t*t^(-1:ℝ)=1 := by rw [Real.rpow_neg_one]; exact mul_inv_cancel₀ ht.ne'
  have hlinQ : 1000*L^2*n/e ≤ T*t^(-a) := by
    have hh := mul_le_mul_of_nonneg_right hT.2.2.1 (Real.rpow_nonneg ht.le (-a))
    have heq : (1000*L^2*n*t^a/e)*t^(-a)=1000*L^2*n/e := by
      calc
        _ = (1000*L^2*n/e)*(t^a*t^(-a)) := by ring
        _ = _ := by rw [htcan,mul_one]
    change _ ≤ T*_ at hh
    rw [show (1000*L^2*n*t^a/incidences P Q)*t^(-a)=1000*L^2*n/e from heq] at hh
    exact hh
  have hlinP : 1000*L^2*m/e ≤ T*t^(-1:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hT.2.2.2.1 (Real.rpow_nonneg ht.le (-1))
    have heq : (1000*L^2*m*t/e)*t^(-1:ℝ)=1000*L^2*m/e := by
      calc
        _ = (1000*L^2*m/e)*(t*t^(-1:ℝ)) := by ring
        _ = _ := by rw [htcan1,mul_one]
    change _ ≤ T*_ at hh
    rw [show (1000*L^2*m*t/incidences P Q)*t^(-1:ℝ)=1000*L^2*m/e from heq] at hh
    exact hh
  have hinc : incidences F G/e≤ T*((u*v)^(2/3:ℝ)+t^(-a)*v+t^(-1:ℝ)*u) := by
    have hh := div_le_div_of_nonneg_right hraw hE.le
    rw [hmul,hcF,hcG] at hh
    have h0 := mul_le_mul_of_nonneg_right hT.2.1 (Real.rpow_nonneg (mul_nonneg hu hv) (2/3:ℝ))
    have h1 := mul_le_mul_of_nonneg_right hlinQ hv
    have h2 := mul_le_mul_of_nonneg_right hlinP hu
    calc
      _ ≤ 1000*L^2*((m*n)^(2/3:ℝ)*(u*v)^(2/3:ℝ)+m*u+n*v)/e := hh
      _ = (1000*L^2*(m*n)^(2/3:ℝ)/e)*(u*v)^(2/3:ℝ)+
          (1000*L^2*m/e)*u+(1000*L^2*n/e)*v := by ring
      _ ≤ _ := by nlinarith only [h0,h1,h2]
  have heP := incidence_degree_le F G (fun p hp =>
    (degree_mono hG p).trans (hP p (hF hp)))
  have heQ := incidence_degree_le G F (fun q hq =>
    (degree_mono hF q).trans (hQ q (hG hq)))
  have hp : incidences F G/e≤ T*u := by
    have hh := div_le_div_of_nonneg_right heP hE.le
    rw [hcF] at hh
    calc
      _ ≤ m*u*dP/e := hh
      _ = (dP*m/e)*u := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hT.2.2.2.2.1 hu
  have hq : incidences F G/e≤ T*v := by
    rw [incidences_comm G F] at heQ
    have hh := div_le_div_of_nonneg_right heQ hE.le
    rw [hcG] at hh
    calc
      _ ≤ n*v*dQ/e := hh
      _ = (dQ*n/e)*v := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hT.2.2.2.2.2 hv
  exact preliminary_square_root hu hv (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg ht.le _)
    (zero_le_one.trans hT.1) hinc hp hq
end
end PlanarUnitDistances.GeometricExpansion

namespace PlanarUnitDistances.GeometricOptimizer
open CircleIncidence CircleCutting IncidenceRegularization GeometricExpansion
open scoped Classical
noncomputable section

def lift (P : Finset Plane) (A : Finset P) : Finset Plane := A.map (Function.Embedding.subtype _)
lemma lift_card (P : Finset Plane) (A : Finset P) : (lift P A).card=A.card := Finset.card_map _
lemma lift_subset (P : Finset Plane) (A : Finset P) : lift P A⊆P := by
  intro p hp
  obtain ⟨q,_,rfl⟩ := Finset.mem_map.mp hp
  exact q.property
lemma lift_univ (P : Finset Plane) : lift P Finset.univ=P := by
  ext p
  simp [lift]
lemma lift_subtype (P A : Finset Plane) (hA : A⊆P) : lift P (A.subtype (·∈P))=A := by
  rw [lift,Finset.subtype_map]
  exact Finset.filter_eq_self.mpr (fun p hp => hA hp)
lemma subtype_subset {P A : Finset Plane} {F : Finset P} (h : A⊆lift P F) :
    A.subtype (·∈P)⊆F := by
  intro p hp
  have hh := h (Finset.mem_subtype.mp hp)
  obtain ⟨q,hq,heq⟩ := Finset.mem_map.mp hh
  have hpq : q=p := Subtype.ext heq
  simpa only [hpq] using hq

def counting (P : Finset Plane) : P → ℝ := fun _ => 1/(P.card:ℝ)
def weight (P Q : Finset Plane) : P → Q → ℝ := fun p q =>
  (if dist (p:Plane) (q:Plane)=1 then (1:ℝ) else 0)/incidences P Q
lemma counting_mass (P : Finset Plane) (A : Finset P) :
    mass (counting P) A=((lift P A).card:ℝ)/(P.card:ℝ) := by
  simp [mass,counting,lift,div_eq_mul_inv]
lemma weight_rect (P Q : Finset Plane) (A : Finset P) (B : Finset Q) :
    rect (weight P Q) A B=incidences (lift P A) (lift Q B)/incidences P Q := by
  unfold rect weight
  simp only [←Finset.sum_div]
  congr 1
  simp only [incidences,degree_sum,lift,Finset.sum_map,Function.Embedding.coe_subtype]
  exact Finset.sum_comm
lemma weight_row (P Q : Finset Plane) (p : P) (B : Finset Q) :
    (∑q∈B,weight P Q p q)=degree (lift Q B) p/incidences P Q := by
  simp only [weight,←Finset.sum_div,degree_sum,lift,Finset.sum_map,Function.Embedding.coe_subtype,dist_comm]

theorem exists_rectangle (P Q : Finset Plane) {L dP dQ t a τ : ℝ}
    (hE : 0< incidences P Q) (hL : 1≤ L)
    (hlP : cuttingLog P.card≤ L) (hlQ : cuttingLog Q.card≤ L)
    (hdP : 0≤ dP) (hdQ : 0≤ dQ) (ht : 0< t)
    (hP : ∀p∈P,degree Q p≤ dP) (hQ : ∀q∈Q,degree P q≤ dQ)
    (hτ : 0< τ) (hτ1 : τ≤ 1) :
    ∃F⊆P,∃G⊆Q,
      let U := (F.card:ℝ)/(P.card:ℝ)
      let V := (G.card:ℝ)/(Q.card:ℝ)
      let W := incidences F G/incidences P Q
      let T := factor (P.card:ℝ) (Q.card:ℝ) (incidences P Q) L dP dQ t a
      let e := Real.sqrt (t^(-a))+Real.sqrt (t^(-1:ℝ))
      let ξ := (T*Real.sqrt (U*V)/W)*((τ/min U V)^(1/6:ℝ)+e)
      τ≤ U ∧ τ≤ V ∧ 0< W ∧ (U*V)^(27/50:ℝ)≤ W ∧
      (∀A⊆F,∀B⊆G,incidences A B/incidences F G≤
        Real.sqrt ((A.card:ℝ)/F.card*((B.card:ℝ)/G.card))*
          (((A.card:ℝ)/F.card*((B.card:ℝ)/G.card))^(1/25:ℝ)+ξ)) ∧
      (τ≤ U-1/(P.card:ℝ) → ∀p∈F,(27/50:ℝ)/(F.card:ℝ)≤ degree G p/incidences F G) ∧
      (τ≤ V-1/(Q.card:ℝ) → ∀q∈G,(27/50:ℝ)/(G.card:ℝ)≤ degree F q/incidences F G) := by
  have hmn : 0<(P.card:ℝ)*(Q.card:ℝ) := hE.trans_le (incidences_le P Q)
  have hm : 0<(P.card:ℝ) := pos_of_mul_pos_left hmn (Nat.cast_nonneg _)
  have hn : 0<(Q.card:ℝ) := pos_of_mul_pos_right hmn (Nat.cast_nonneg _)
  have hμ : ∀p,0≤ counting P p := fun _ => div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hν : ∀q,0≤ counting Q q := fun _ => div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hμs : ∑p,counting P p=1 := by
    change mass (counting P) Finset.univ=1
    rw [counting_mass,lift_univ,div_self hm.ne']
  have hνs : ∑q,counting Q q=1 := by
    change mass (counting Q) Finset.univ=1
    rw [counting_mass,lift_univ,div_self hn.ne']
  have hws : ∑p,∑q,weight P Q p q=1 := by
    change rect (weight P Q) Finset.univ Finset.univ=1
    rw [weight_rect,lift_univ,lift_univ,div_self hE.ne']
  obtain ⟨F,G,hmax,hwin⟩ := exists_maximizing (counting P) (counting Q) (weight P Q)
    (γ:=(1/2:ℝ)+1/25) hτ1 hμs hνs hws
  obtain ⟨hU,hV,hW,hpow⟩ := winner_positive (counting P) (counting Q) (weight P Q) hτ hmax hwin
  let T := factor (P.card:ℝ) (Q.card:ℝ) (incidences P Q) L dP dQ t a
  let err := Real.sqrt (t^(-a))+Real.sqrt (t^(-1:ℝ))
  have hT0 : 0≤ T := zero_le_one.trans (factor_bounds (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hE hdP hdQ ht (a:=a) (L:=L)).1
  have hpre (A : Finset P) (B : Finset Q) : rect (weight P Q) A B≤
      T*Real.sqrt (mass (counting P) A*mass (counting Q) B)*
        ((mass (counting P) A*mass (counting Q) B)^(1/6:ℝ)+err) := by
    rw [weight_rect,counting_mass,counting_mass]
    simpa only [T,err,add_assoc] using preliminary (a:=a) P Q hE hL hlP hlQ hdP hdQ ht hP hQ (lift P A) (lift_subset P A)
      (lift Q B) (lift_subset Q B)
  have hexp := maximizing_expansion (counting P) (counting Q) (weight P Q)
    hμ hν hμs hνs hτ (by norm_num : (0:ℝ)≤ 1/25) (by norm_num : (0:ℝ)≤ 1/6)
    hT0 (show 0≤ err by dsimp [err]; positivity) hmax hW hpre
  let FP := lift P F
  let GQ := lift Q G
  have hFP : 0<(FP.card:ℝ) := by
    have hh := hU
    rw [counting_mass] at hh
    exact (div_pos_iff_of_pos_right hm).mp hh
  have hGQ : 0<(GQ.card:ℝ) := by
    have hh := hV
    rw [counting_mass] at hh
    exact (div_pos_iff_of_pos_right hn).mp hh
  have hFG : 0< incidences FP GQ := by
    rw [weight_rect] at hW
    exact (div_pos_iff_of_pos_right hE).mp hW
  refine ⟨FP,lift_subset P F,GQ,lift_subset Q G,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [counting_mass] using hmax.1
  · simpa only [counting_mass] using hmax.2.1
  · simpa only [weight_rect] using hW
  · norm_num only at hpow
    simpa only [counting_mass,weight_rect] using hpow
  · intro A hA B hB
    let As := A.subtype (·∈P)
    let Bs := B.subtype (·∈Q)
    have hAP : A⊆P := hA.trans (lift_subset P F)
    have hBQ : B⊆Q := hB.trans (lift_subset Q G)
    have hAs : lift P As=A := lift_subtype P A hAP
    have hBs : lift Q Bs=B := lift_subtype Q B hBQ
    have hh := hexp As (subtype_subset hA) Bs (subtype_subset hB)
    simp only [counting_mass,weight_rect,hAs,hBs] at hh
    have hnormA : ((A.card:ℝ)/P.card)/((FP.card:ℝ)/P.card)=(A.card:ℝ)/FP.card := by field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne',hE.ne',hFG.ne']
    have hnormB : ((B.card:ℝ)/Q.card)/((GQ.card:ℝ)/Q.card)=(B.card:ℝ)/GQ.card := by field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne',hE.ne',hFG.ne']
    have hnormE : (incidences A B/incidences P Q)/(incidences FP GQ/incidences P Q)=
        incidences A B/incidences FP GQ := by field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne',hE.ne',hFG.ne']
    dsimp only [FP,GQ] at hnormA hnormB hnormE
    simpa only [hnormA,hnormB,hnormE,FP,GQ,T,err] using hh
  · intro he p hp
    obtain ⟨ps,hps,hpseq⟩ := Finset.mem_map.mp hp
    have her : τ≤ mass (counting P) (F.erase ps) := by
      have hh : mass (counting P) (F.erase ps)+counting P ps=mass (counting P) F :=
        Finset.sum_erase_add _ _ hps
      simp only [counting_mass,counting] at hh ⊢
      dsimp only [FP,GQ] at he
      linarith
    have hh := left_atom_bound (counting P) (counting Q) (weight P Q) hμ hτ
      (by norm_num : (0:ℝ)≤ 1/2+1/25) (by norm_num : (1/2:ℝ)+1/25≤ 1) hmax hW hps her
    rw [counting_mass,weight_row,weight_rect] at hh
    norm_num only at hh
    have hca : counting P ps/((FP.card:ℝ)/P.card)=1/(FP.card:ℝ) := by dsimp [counting]; field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne']
    have hce : (degree GQ ps/incidences P Q)/(incidences FP GQ/incidences P Q)=degree GQ ps/incidences FP GQ := by field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne',hE.ne',hFG.ne']
    rw [hca,hce] at hh
    change (ps:Plane)=p at hpseq
    simpa only [hpseq,mul_one_div] using hh
  · intro he q hq
    obtain ⟨qs,hqs,hqseq⟩ := Finset.mem_map.mp hq
    have her : τ≤ mass (counting Q) (G.erase qs) := by
      have hh : mass (counting Q) (G.erase qs)+counting Q qs=mass (counting Q) G :=
        Finset.sum_erase_add _ _ hqs
      simp only [counting_mass,counting] at hh ⊢
      dsimp only [FP,GQ] at he
      linarith
    have hh := right_atom_bound (counting P) (counting Q) (weight P Q) hν hτ
      (by norm_num : (0:ℝ)≤ 1/2+1/25) (by norm_num : (1/2:ℝ)+1/25≤ 1) hmax hW hqs her
    have hcol : (∑p∈F,weight P Q p qs)=degree FP qs/incidences P Q := by
      simp only [weight,←Finset.sum_div,degree_sum,FP,lift,Finset.sum_map,Function.Embedding.coe_subtype]
      congr 1

    rw [counting_mass,hcol,weight_rect] at hh
    norm_num only at hh
    have hca : counting Q qs/((GQ.card:ℝ)/Q.card)=1/(GQ.card:ℝ) := by dsimp [counting]; field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne']
    have hce : (degree FP qs/incidences P Q)/(incidences FP GQ/incidences P Q)=degree FP qs/incidences FP GQ := by field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne',hE.ne',hFG.ne']
    rw [hca,hce] at hh
    change (qs:Plane)=q at hqseq
    simpa only [hqseq,mul_one_div] using hh
end
end PlanarUnitDistances.GeometricOptimizer

namespace PlanarUnitDistances.IncidenceRegularization
open Real

lemma winning_product {U V W T τ η ρ e : ℝ}
    (hτ : 0 < τ) (hU : τ ≤ U) (hV : τ ≤ V)
    (hT : 0 < T) (hη : 0 ≤ η) (he : 0 ≤ e)
    (hwin : (U*V)^((1:ℝ)/2+η) ≤ W)
    (hpre : W ≤ T*sqrt (U*V)*((U*V)^ρ+e))
    (herr : T*e*(τ^2)^(-η) ≤ 1/2) :
    1/2 ≤ T*(U*V)^(ρ-η) := by
  have hUp := hτ.trans_le hU
  have hVp := hτ.trans_le hV
  have hUV := mul_pos hUp hVp
  have heq : (U*V)^((1:ℝ)/2+η)=sqrt (U*V)*(U*V)^η := by
    rw [Real.rpow_add hUV,Real.sqrt_eq_rpow]
  have hw : (U*V)^η ≤ T*((U*V)^ρ+e) := by
    apply (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr hUV)).mp
    calc
      _ = (U*V)^((1:ℝ)/2+η) := by simpa only [mul_comm] using heq.symm
      _ ≤ W := hwin
      _ ≤ _ := hpre
      _ = _ := by ring
  have hw' := mul_le_mul_of_nonneg_right hw (Real.rpow_pos_of_pos hUV (-η)).le
  have hone : (U*V)^η*(U*V)^(-η)=1 := by rw [←Real.rpow_add hUV]; simp
  have hp : (U*V)^ρ*(U*V)^(-η)=(U*V)^(ρ-η) := by rw [←Real.rpow_add hUV]; rfl
  rw [hone] at hw'
  have hfeas : τ^2 ≤ U*V := by nlinarith [mul_le_mul hU hV hτ.le hUp.le]
  have hpow : (U*V)^(-η) ≤ (τ^2)^(-η) :=
    Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hτ) hfeas (by linarith)
  have herr' := (mul_le_mul_of_nonneg_left hpow (mul_nonneg hT.le he)).trans herr
  have hh : T*((U*V)^ρ+e)*(U*V)^(-η)=T*(U*V)^(ρ-η)+T*e*(U*V)^(-η) := by
    rw [mul_add,add_mul,mul_assoc,hp]
  rw [hh] at hw'
  linarith

lemma winning_product_lower {U V W T τ η ρ e : ℝ}
    (hτ : 0 < τ) (hU : τ ≤ U) (hV : τ ≤ V)
    (hT : 0 < T) (hη : 0 ≤ η) (he : 0 ≤ e) (hρη : η < ρ)
    (hwin : (U*V)^((1:ℝ)/2+η) ≤ W)
    (hpre : W ≤ T*sqrt (U*V)*((U*V)^ρ+e))
    (herr : T*e*(τ^2)^(-η) ≤ 1/2) :
    (1/(2*T))^(1/(ρ-η)) ≤ U*V := by
  have hh := winning_product hτ hU hV hT hη he hwin hpre herr
  have hp : 1/(2*T) ≤ (U*V)^(ρ-η) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*T)).mpr
    linarith
  have hUp := hτ.trans_le hU
  have hVp := hτ.trans_le hV
  have hpos : 0 < ρ-η := sub_pos.mpr hρη
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ 1/(2*T)) hp
    (by positivity : 0 ≤ 1/(ρ-η))
  simpa only [one_div,Real.rpow_rpow_inv (mul_pos hUp hVp).le hpos.ne'] using hr
end PlanarUnitDistances.IncidenceRegularization

namespace PlanarUnitDistances.OptimizerPowers
open Filter PowerGrowth IncidenceRegularization GeometricExpansion
open scoped Classical
noncomputable section

lemma factor_upper {t m n e L : ℕ → ℝ} {a b : ℝ}
    (ht : Tendsto t atTop atTop) (_ha : 0 < a) (_ha1 : a < 1) (hb : 0 < b)
    (hm : Upper atTop t m (1+2*a)) (hn : Upper atTop t n (2+a))
    (he : Lower atTop t e (2+2*a)) (hL : Upper atTop t L 0)
    (hm0 : ∀ᶠi in atTop,0 ≤ m i) (hn0 : ∀ᶠi in atTop,0 ≤ n i)
    (hL0 : ∀ᶠi in atTop,0 ≤ L i) :
    Upper atTop t (fun i => factor (m i) (n i) (e i) (L i)
      ((t i)^(1+b)) ((t i)^(a+b)) (t i) a) b := by
  have he0 := he.eventually_pos ht
  have ht0 := eventually_base_pos ht
  have hC : Upper atTop t (fun i => 1000*(L i)^2) 0 := by
    have h := (hL.mul hL hL0 hL0 ht).const_mul ht (by norm_num : (0:ℝ) ≤ 1000)
    convert h using 1 <;> ring_nf
  have hC0 : ∀ᶠi in atTop,0 ≤ 1000*(L i)^2 := Eventually.of_forall fun i => by positivity
  have hmn := (hm.mul hn hm0 hn0 ht).rpow (by filter_upwards [hm0,hn0] with i hi hj; positivity)
    ht (by norm_num : (0:ℝ) < 2/3)
  have hmix := (hC.mul hmn hC0 (by filter_upwards [hm0,hn0] with i hi hj; exact Real.rpow_nonneg (mul_nonneg hi hj) _) ht).div he he0 ht
  have h1 : Upper atTop t (fun i => 1000*(L i)^2*(m i*n i)^(2/3:ℝ)/e i) b :=
    hmix.exponent_mono (by linarith) ht
  have hna := hn.mul (upper_rpow ht a) hn0
    (by filter_upwards [ht0] with i hi; positivity) ht
  have h2' := (hC.mul hna hC0 (by filter_upwards [hn0,ht0] with i hi hj; positivity) ht).div he he0 ht
  have h2 : Upper atTop t (fun i => 1000*(L i)^2*n i*(t i)^a/e i) b := by
    have hh := h2'.exponent_mono (show 0+(2+a+a)-(2+2*a) ≤ b by linarith) ht
    convert hh using 1; ring_nf
  have hmt := hm.mul (upper_rpow ht 1) hm0 (by filter_upwards [ht0] with i hi; positivity) ht
  have h3' := (hC.mul hmt hC0 (by filter_upwards [hm0,ht0] with i hi hj; positivity) ht).div he he0 ht
  have h3 : Upper atTop t (fun i => 1000*(L i)^2*m i*t i/e i) b := by
    have hh := h3'.exponent_mono (show 0+(1+2*a+1)-(2+2*a) ≤ b by linarith) ht
    simpa only [Real.rpow_one,mul_assoc] using hh
  have h4' := ((upper_rpow ht (1+b)).mul hm (by filter_upwards [ht0] with i hi; positivity) hm0 ht).div he he0 ht
  have h4 : Upper atTop t (fun i => (t i)^(1+b)*m i/e i) b := by
    convert h4' using 1; ring
  have h5' := ((upper_rpow ht (a+b)).mul hn (by filter_upwards [ht0] with i hi; positivity) hn0 ht).div he he0 ht
  have h5 : Upper atTop t (fun i => (t i)^(a+b)*n i/e i) b := by
    convert h5' using 1; ring
  exact (((((upper_const ht 1).exponent_mono hb.le ht).add h1 ht).add h2 ht).add h3 ht).add h4 ht |>.add h5 ht

theorem winning_powers {t U V W T : ℕ → ℝ} {a b : ℝ}
    (ht : Tendsto t atTop atTop) (_ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hba : b < a/1000)
    (hT : Upper atTop t T b)
    (hdata : ∀ᶠi in atTop,
      1 ≤ T i ∧ (t i)^(-a/8) ≤ U i ∧ (t i)^(-a/8) ≤ V i ∧
      U i ≤ 1 ∧ V i ≤ 1 ∧ 0 < W i ∧
      (U i*V i)^(27/50:ℝ) ≤ W i ∧
      W i ≤ T i*Real.sqrt (U i*V i)*((U i*V i)^(1/6:ℝ)+
        (Real.sqrt ((t i)^(-a))+Real.sqrt ((t i)^(-1:ℝ))))) :
    Lower atTop t (fun i => U i*V i) (-9*b) ∧
    Lower atTop t U (-9*b) ∧ Lower atTop t V (-9*b) ∧
    Lower atTop t W (-5*b) ∧
    Tendsto (fun i => (T i*Real.sqrt (U i*V i)/W i)*
      ((((t i)^(-a/8))/min (U i) (V i))^(1/6:ℝ)+
        (Real.sqrt ((t i)^(-a))+Real.sqrt ((t i)^(-1:ℝ))))) atTop (nhds 0) := by
  let err := fun i => Real.sqrt ((t i)^(-a))+Real.sqrt ((t i)^(-1:ℝ))
  have ht0 := eventually_base_pos ht
  have herr1 : Upper atTop t (fun i => Real.sqrt ((t i)^(-a))) (-a/2) := by
    have hh := (upper_rpow ht (-a)).rpow (by filter_upwards [ht0] with i hi; positivity) ht
      (by norm_num : (0:ℝ) < 1/2)
    simpa only [Real.sqrt_eq_rpow,div_eq_mul_inv,one_mul] using hh
  have herr2 : Upper atTop t (fun i => Real.sqrt ((t i)^(-1:ℝ))) (-a/2) := by
    have hh := (upper_rpow ht (-1)).rpow (by filter_upwards [ht0] with i hi; positivity) ht
      (by norm_num : (0:ℝ) < 1/2)
    have hh' := hh.exponent_mono (show (-1:ℝ)*(1/2) ≤ -a/2 by linarith) ht
    simpa only [Real.sqrt_eq_rpow] using hh'
  have herr := herr1.add herr2 ht
  have hT0 : ∀ᶠi in atTop,0 ≤ T i := hdata.mono fun i hi => zero_le_one.trans hi.1
  have hTpos : ∀ᶠi in atTop,0 < T i := hdata.mono fun i hi => zero_lt_one.trans_le hi.1
  have herr0 : ∀ᶠi in atTop,0 ≤ err i := Eventually.of_forall fun i => by dsimp [err]; positivity
  have hfloor : Upper atTop t (fun i => (((t i)^(-a/8))^2)^(-(1/25:ℝ))) (a/100) := by
    apply (upper_rpow ht (a/100)).congr
    filter_upwards [ht0] with i hi
    rw [←Real.rpow_natCast,←Real.rpow_mul hi.le,←Real.rpow_mul hi.le]
    congr 1
    ring
  have hfloor0 : ∀ᶠi in atTop,0 ≤ (((t i)^(-a/8))^2)^(-(1/25:ℝ)) :=
    Eventually.of_forall fun i => Real.rpow_nonneg (sq_nonneg _) _
  have hsmall := ((hT.mul herr hT0 herr0 ht).mul hfloor
    (by filter_upwards [hT0,herr0] with i hi hj; positivity) hfloor0 ht).tendsto_zero
      (by filter_upwards [hT0,herr0,hfloor0] with i hi hj hk; positivity) ht
      (show b+(-a/2)+a/100 < 0 by linarith)
  have hevent := hsmall.eventually_le_const (by norm_num : (0:ℝ) < 1/2)
  have hLB := (((lower_const ht (by norm_num : (0:ℝ) < 1/2)).div hT hTpos ht).rpow ht
    (by norm_num : (0:ℝ) < 150/19))
  have hUV : Lower atTop t (fun i => U i*V i) (-9*b) := by
    apply (hLB.exponent_mono (show -9*b ≤ (0-b)*(150/19) by linarith) ht).mono
    filter_upwards [hdata,ht0,hevent] with i hi hti he
    have hh := winning_product_lower (Real.rpow_pos_of_pos hti (-a/8)) hi.2.1 hi.2.2.1
      (zero_lt_one.trans_le hi.1) (by norm_num : (0:ℝ) ≤ 1/25)
      (show 0 ≤ err i by dsimp [err]; positivity) (by norm_num : (1/25:ℝ) < 1/6)
      (by norm_num; exact hi.2.2.2.2.2.2.1) hi.2.2.2.2.2.2.2 he
    norm_num only at hh
    convert hh using 1; ring_nf
  have huv0 : ∀ᶠi in atTop,0 < U i ∧ 0 < V i := by
    filter_upwards [hdata,ht0] with i hi hti
    exact ⟨(Real.rpow_pos_of_pos hti _).trans_le hi.2.1,(Real.rpow_pos_of_pos hti _).trans_le hi.2.2.1⟩
  have hU : Lower atTop t U (-9*b) := hUV.mono (by
    filter_upwards [hdata,huv0] with i hi hj
    exact mul_le_of_le_one_right hj.1.le hi.2.2.2.2.1)
  have hV : Lower atTop t V (-9*b) := hUV.mono (by
    filter_upwards [hdata,huv0] with i hi hj
    exact mul_le_of_le_one_left hj.2.le hi.2.2.2.1)
  have hW : Lower atTop t W (-5*b) := by
    apply ((hUV.rpow ht (by norm_num : (0:ℝ) < 27/50)).exponent_mono
      (show -5*b ≤ -9*b*(27/50) by linarith) ht).mono
    exact hdata.mono fun i hi => hi.2.2.2.2.2.2.1
  have hmin : Lower atTop t (fun i => min (U i) (V i)) (-9*b) := by
    intro ε hε
    filter_upwards [hU ε hε,hV ε hε] with i hi hj
    exact le_min hi hj
  have hmin0 := hmin.eventually_pos ht
  have hquot := (upper_rpow ht (-a/8)).div hmin hmin0 ht
  have hqpow := hquot.rpow (by filter_upwards [ht0,hmin0] with i hi hj; positivity) ht
    (by norm_num : (0:ℝ) < 1/6)
  have hinside : Upper atTop t (fun i => (((t i)^(-a/8))/min (U i) (V i))^(1/6:ℝ)+err i)
      (-a/48+3*b/2) := by
    have hh : Upper atTop t (fun i => (((t i)^(-a/8))/min (U i) (V i))^(1/6:ℝ)) (-a/48+3*b/2) := by
      convert hqpow using 1; ring
    exact hh.add (herr.exponent_mono (by linarith) ht) ht
  have hsqrt : Upper atTop t (fun i => Real.sqrt (U i*V i)) 0 := by
    apply (upper_const ht 1).mono
    filter_upwards [hdata,huv0] with i hi hj
    apply (Real.sqrt_le_one).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hi.2.2.2.1) (sub_nonneg.mpr hi.2.2.2.2.1)]
  have hpref := (hT.mul hsqrt hT0 (Eventually.of_forall fun i => Real.sqrt_nonneg _) ht).div hW (hW.eventually_pos ht) ht
  have hfin := hpref.mul hinside (by filter_upwards [hT0,hW.eventually_pos ht] with i hi hj; positivity)
    (by filter_upwards [ht0,hmin0] with i hi hj; dsimp [err]; positivity) ht
  refine ⟨hUV,hU,hV,hW,?_⟩
  exact hfin.tendsto_zero (by filter_upwards [hT0,hW.eventually_pos ht,ht0,hmin0] with i hi hj hk hl; dsimp [err]; positivity)
    ht (by linarith)
end
end PlanarUnitDistances.OptimizerPowers

namespace PlanarUnitDistances.RegularizedPiece
open Filter PowerGrowth CircleIncidence CircleCutting GeometricExpansion GeometricOptimizer OptimizerPowers
open scoped Classical
noncomputable section

lemma eventually_choose {ι A : Type*} [Nonempty A] {F : Filter ι} {R : ι → A → Prop}
    (h : ∀ᶠi in F,∃x,R i x) : ∃f : ι → A,∀ᶠi in F,R i (f i) := by
  let f : ι → A := fun i => if hi : ∃x,R i x then Classical.choose hi else Classical.choice inferInstance
  refine ⟨f,h.mono ?_⟩
  intro i hi
  simp only [f,dite_eq_left hi]
  exact Classical.choose_spec hi

theorem regularize {t : ℕ → ℝ} {X P Q : ℕ → Finset Plane}
    (ht : Tendsto t atTop atTop) (ht1 : ∀i,1 ≤ t i)
    (hX : Upper atTop t (fun i => ((X i).card:ℝ)) 3)
    (hPX : ∀i,P i ⊆ X i) (hQX : ∀i,Q i ⊆ X i)
    {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hba : b < a/1000)
    (hP : Upper atTop t (fun i => ((P i).card:ℝ)) (1+2*a))
    (hQ : Upper atTop t (fun i => ((Q i).card:ℝ)) (2+a))
    (hE : Lower atTop t (fun i => incidences (P i) (Q i)) (2+2*a))
    (hdP : ∀i,∀p∈P i,degree (Q i) p ≤ (t i)^(1+b))
    (hdQ : ∀i,∀q∈Q i,degree (P i) q ≤ (t i)^(a+b)) :
    ∃F G : ℕ → Finset Plane,∃ξ : ℕ → ℝ,
      Tendsto ξ atTop (nhds 0) ∧
      Upper atTop t (fun i => ((F i).card:ℝ)) (1+2*a) ∧
      Upper atTop t (fun i => ((G i).card:ℝ)) (2+a) ∧
      Lower atTop t (fun i => ((F i).card:ℝ)) (1+2*a-10*b) ∧
      Lower atTop t (fun i => ((G i).card:ℝ)) (2+a-10*b) ∧
      Lower atTop t (fun i => incidences (F i) (G i)) (2+2*a-5*b) ∧
      (∀ᶠi in atTop,F i ⊆ P i ∧ G i ⊆ Q i ∧ 0 ≤ ξ i ∧
        0 < incidences (F i) (G i) ∧
        (∀A⊆F i,∀B⊆G i,incidences A B/incidences (F i) (G i) ≤
          Real.sqrt ((A.card:ℝ)/(F i).card*((B.card:ℝ)/(G i).card))*
            (((A.card:ℝ)/(F i).card*((B.card:ℝ)/(G i).card))^(1/25:ℝ)+ξ i)) ∧
        (∀p∈F i,(27/50:ℝ)/((F i).card:ℝ) ≤ degree (G i) p/incidences (F i) (G i)) ∧
        (∀q∈G i,(27/50:ℝ)/((G i).card:ℝ) ≤ degree (F i) q/incidences (F i) (G i))) := by
  let m : ℕ → ℝ := fun i => (P i).card
  let n : ℕ → ℝ := fun i => (Q i).card
  let e : ℕ → ℝ := fun i => incidences (P i) (Q i)
  let L : ℕ → ℝ := fun i => cuttingLog (X i).card
  let T : ℕ → ℝ := fun i => factor (m i) (n i) (e i) (L i) ((t i)^(1+b)) ((t i)^(a+b)) (t i) a
  let τ : ℕ → ℝ := fun i => (t i)^(-a/8)
  let err : ℕ → ℝ := fun i => Real.sqrt ((t i)^(-a))+Real.sqrt ((t i)^(-1:ℝ))
  have ht0 (i : ℕ) : 0 < t i := zero_lt_one.trans_le (ht1 i)
  have he0 := hE.eventually_pos ht
  have hmp : ∀ᶠi in atTop,0 < m i := by
    filter_upwards [he0] with i hi
    exact pos_of_mul_pos_left (hi.trans_le (incidences_le (P i) (Q i))) (Nat.cast_nonneg _)
  have hnp : ∀ᶠi in atTop,0 < n i := by
    filter_upwards [he0] with i hi
    exact pos_of_mul_pos_right (hi.trans_le (incidences_le (P i) (Q i))) (Nat.cast_nonneg _)
  have hmL : Lower atTop t m (1+2*a-b) := by
    have hh := hE.div (upper_rpow ht (1+b)) (Eventually.of_forall fun i => Real.rpow_pos_of_pos (ht0 i) _) ht
    have hh' := hh.mono (Eventually.of_forall fun i => (div_le_iff₀ (Real.rpow_pos_of_pos (ht0 i) _)).mpr (incidence_degree_le (P i) (Q i) (hdP i)))
    convert hh' using 1; ring
  have hnL : Lower atTop t n (2+a-b) := by
    have hh := hE.div (upper_rpow ht (a+b)) (Eventually.of_forall fun i => Real.rpow_pos_of_pos (ht0 i) _) ht
    have hh' := hh.mono (Eventually.of_forall fun i => (div_le_iff₀ (Real.rpow_pos_of_pos (ht0 i) _)).mpr (by simpa only [incidences_comm] using incidence_degree_le (Q i) (P i) (hdQ i)))
    convert hh' using 1; ring
  have hlog := CuttingAsymptotics.cuttingLog_upper ht hX
  have hTu : Upper atTop t T b := factor_upper ht ha ha1 hb hP hQ hE hlog
    (Eventually.of_forall fun i => Nat.cast_nonneg _) (Eventually.of_forall fun i => Nat.cast_nonneg _)
    (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _))
  let R := fun i (fg : Finset Plane×Finset Plane) =>
    fg.1 ⊆ P i ∧ fg.2 ⊆ Q i ∧
    let U := (fg.1.card:ℝ)/m i
    let V := (fg.2.card:ℝ)/n i
    let W := incidences fg.1 fg.2/e i
    let ξ := (T i*Real.sqrt (U*V)/W)*((τ i/min U V)^(1/6:ℝ)+err i)
    τ i ≤ U ∧ τ i ≤ V ∧ 0 < W ∧ (U*V)^(27/50:ℝ) ≤ W ∧
      (∀A⊆fg.1,∀B⊆fg.2,incidences A B/incidences fg.1 fg.2 ≤
        Real.sqrt ((A.card:ℝ)/fg.1.card*((B.card:ℝ)/fg.2.card))*
          (((A.card:ℝ)/fg.1.card*((B.card:ℝ)/fg.2.card))^(1/25:ℝ)+ξ)) ∧
      (τ i ≤ U-1/m i → ∀p∈fg.1,(27/50:ℝ)/(fg.1.card:ℝ) ≤ degree fg.2 p/incidences fg.1 fg.2) ∧
      (τ i ≤ V-1/n i → ∀q∈fg.2,(27/50:ℝ)/(fg.2.card:ℝ) ≤ degree fg.1 q/incidences fg.1 fg.2)
  have hr : ∀ᶠi in atTop,∃fg,R i fg := by
    filter_upwards [he0] with i hi
    obtain ⟨F,hF,G,hG,h⟩ := exists_rectangle (P i) (Q i) hi (cuttingLog_one_le _)
      (cuttingLog_mono (Finset.card_le_card (hPX i))) (cuttingLog_mono (Finset.card_le_card (hQX i)))
      (Real.rpow_pos_of_pos (ht0 i) _).le (Real.rpow_pos_of_pos (ht0 i) _).le (ht0 i) (hdP i) (hdQ i)
      (Real.rpow_pos_of_pos (ht0 i) (-a/8)) (Real.rpow_le_one_of_one_le_of_nonpos (ht1 i) (by linarith : -a/8 ≤ 0))
    exact ⟨(F,G),hF,hG,h⟩
  obtain ⟨fg,hfg⟩ := eventually_choose hr
  let F := fun i => (fg i).1
  let G := fun i => (fg i).2
  let U := fun i => ((F i).card:ℝ)/m i
  let V := fun i => ((G i).card:ℝ)/n i
  let W := fun i => incidences (F i) (G i)/e i
  let ξ := fun i => (T i*Real.sqrt (U i*V i)/W i)*((τ i/min (U i) (V i))^(1/6:ℝ)+err i)
  have hdata : ∀ᶠi in atTop,1 ≤ T i ∧ τ i ≤ U i ∧ τ i ≤ V i ∧ U i ≤ 1 ∧ V i ≤ 1 ∧
      0 < W i ∧ (U i*V i)^(27/50:ℝ) ≤ W i ∧
      W i ≤ T i*Real.sqrt (U i*V i)*((U i*V i)^(1/6:ℝ)+err i) := by
    filter_upwards [hfg,he0,hmp,hnp] with i hi hei hmi hni
    obtain ⟨hF,hG,hU,hV,hW,hpow,_,_,_⟩ := hi
    refine ⟨(factor_bounds (Nat.cast_nonneg _) (Nat.cast_nonneg _) hei
      (Real.rpow_pos_of_pos (ht0 i) _).le (Real.rpow_pos_of_pos (ht0 i) _).le (ht0 i)).1,hU,hV,?_,?_,hW,hpow,?_⟩
    · exact (div_le_one hmi).mpr (Nat.cast_le.mpr (Finset.card_le_card hF))
    · exact (div_le_one hni).mpr (Nat.cast_le.mpr (Finset.card_le_card hG))
    · simpa only [T,U,V,W,err,m,n,e,L,add_assoc] using preliminary (P i) (Q i) hei (cuttingLog_one_le _)
        (cuttingLog_mono (Finset.card_le_card (hPX i))) (cuttingLog_mono (Finset.card_le_card (hQX i)))
        (Real.rpow_pos_of_pos (ht0 i) _).le (Real.rpow_pos_of_pos (ht0 i) _).le (ht0 i) (hdP i) (hdQ i) (F i) hF (G i) hG
  obtain ⟨_,hUL,hVL,hWL,hξ⟩ := winning_powers ht ha ha1 hb hba hTu hdata
  have hFL : Lower atTop t (fun i => ((F i).card:ℝ)) (1+2*a-10*b) := by
    have hh := hmL.mul hUL ht
    have heq : (fun i => m i*U i) =ᶠ[atTop] (fun i => ((F i).card:ℝ)) := by
      filter_upwards [hmp] with i hi
      dsimp only [U]
      exact mul_div_cancel₀ _ hi.ne'
    convert hh.congr heq using 1; ring
  have hGL : Lower atTop t (fun i => ((G i).card:ℝ)) (2+a-10*b) := by
    have hh := hnL.mul hVL ht
    have heq : (fun i => n i*V i) =ᶠ[atTop] (fun i => ((G i).card:ℝ)) := by
      filter_upwards [hnp] with i hi
      dsimp only [V]
      exact mul_div_cancel₀ _ hi.ne'
    convert hh.congr heq using 1; ring
  have hEL : Lower atTop t (fun i => incidences (F i) (G i)) (2+2*a-5*b) := by
    have hh := hE.mul hWL ht
    have heq : (fun i => e i*W i) =ᶠ[atTop] (fun i => incidences (F i) (G i)) := by
      filter_upwards [he0] with i hi
      dsimp only [W]
      exact mul_div_cancel₀ _ hi.ne'
    convert hh.congr heq using 1; ring
  have hτU := (upper_rpow ht (-a/8)).ratio_zero hUL (Eventually.of_forall fun i => (Real.rpow_pos_of_pos (ht0 i) _).le) ht (by linarith : -a/8 < -9*b)
  have hτV := (upper_rpow ht (-a/8)).ratio_zero hVL (Eventually.of_forall fun i => (Real.rpow_pos_of_pos (ht0 i) _).le) ht (by linarith : -a/8 < -9*b)
  have hmU := (upper_const ht 1).ratio_zero (hmL.mul hUL ht) (Eventually.of_forall fun _ => zero_le_one) ht (by linarith : 0 < 1+2*a-b+ -9*b)
  have hnV := (upper_const ht 1).ratio_zero (hnL.mul hVL ht) (Eventually.of_forall fun _ => zero_le_one) ht (by linarith : 0 < 2+a-b+ -9*b)
  refine ⟨F,G,ξ,hξ,hP.mono (hfg.mono fun i hi => Nat.cast_le.mpr (Finset.card_le_card hi.1)),
    hQ.mono (hfg.mono fun i hi => Nat.cast_le.mpr (Finset.card_le_card hi.2.1)),hFL,hGL,hEL,?_⟩
  filter_upwards [hfg,he0,hmp,hnp,hUL.eventually_pos ht,hVL.eventually_pos ht,hWL.eventually_pos ht,
    hτU.eventually_le_const (by norm_num : (0:ℝ) < 1/2),hτV.eventually_le_const (by norm_num : (0:ℝ) < 1/2),
    hmU.eventually_le_const (by norm_num : (0:ℝ) < 1/2),hnV.eventually_le_const (by norm_num : (0:ℝ) < 1/2),
    hEL.eventually_pos ht] with i hi hei hmi hni hui hvi hwi htu htv hmu hnv heli
  obtain ⟨hF,hG,_,_,_,_,hexp,hp,hq⟩ := hi
  have hfeasP : τ i ≤ U i-1/m i := by
    have h1 := (div_le_iff₀ hui).mp htu
    have h2 := (div_le_iff₀ (mul_pos hmi hui)).mp hmu
    have h3 : 1/m i ≤ U i/2 := (div_le_iff₀ hmi).mpr (by nlinarith)
    linarith
  have hfeasQ : τ i ≤ V i-1/n i := by
    have h1 := (div_le_iff₀ hvi).mp htv
    have h2 := (div_le_iff₀ (mul_pos hni hvi)).mp hnv
    have h3 : 1/n i ≤ V i/2 := (div_le_iff₀ hni).mpr (by nlinarith)
    linarith
  refine ⟨hF,hG,?_,heli,hexp,hp hfeasP,hq hfeasQ⟩
  dsimp only [ξ,err,τ]
  have hTi : 0 ≤ T i := zero_le_one.trans (factor_bounds (Nat.cast_nonneg _) (Nat.cast_nonneg _) hei
    (Real.rpow_pos_of_pos (ht0 i) _).le (Real.rpow_pos_of_pos (ht0 i) _).le (ht0 i)).1
  have hmin : 0 < min (U i) (V i) := lt_min hui hvi
  exact mul_nonneg (div_nonneg (mul_nonneg hTi (Real.sqrt_nonneg _)) hwi.le)
    (add_nonneg (Real.rpow_nonneg (div_nonneg (Real.rpow_nonneg (ht0 i).le _) hmin.le) _)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
end
end PlanarUnitDistances.RegularizedPiece

end OAI
