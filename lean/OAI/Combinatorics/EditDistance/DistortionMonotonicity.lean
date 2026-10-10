import OAI.Combinatorics.EditDistance.Distortion
import OAI.Combinatorics.EditDistance.Metric

namespace OAI

/-!
# Restriction and monotonicity of least distortion
-/

namespace EditDistortion
universe u v

lemma leastDistortion_le {X : Type u} [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hd : ∀ x, ρ x x = 0)
    (hp : ∀ x y, x ≠ y → 0 < ρ x y) (f : X ↪ L1) : leastDistortion ρ ≤ distortion ρ f := by
  apply csInf_le (s := Set.range (distortion ρ)) (a := distortion ρ f) ?_ ⟨f,rfl⟩
  refine ⟨0,?_⟩
  rintro r ⟨g,rfl⟩
  exact distortion_nonneg ρ hd hp g

lemma distortion_le_of_bounds {X : Type u} [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hp : ∀ x y, x ≠ y → 0 < ρ x y)
    (f : X ↪ L1) {U V : ℝ} (hU : 0 ≤ U)
    (hu : ∀ x y, ‖f x-f y‖ ≤ U*ρ x y)
    (hv : ∀ x y, ρ x y ≤ V*‖f x-f y‖) : distortion ρ f ≤ U*V := by
  have hn (x y : X) (hxy : x ≠ y) : 0 < ‖f x-f y‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hxy (f.injective h)))
  obtain ⟨x,y,hxy⟩ := exists_pair_ne X
  have hn1 : {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x-f y‖/ρ x y}.Nonempty :=
    ⟨_,⟨x,y,hxy,rfl⟩⟩
  have hn2 : {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y/‖f x-f y‖}.Nonempty :=
    ⟨_,⟨x,y,hxy,rfl⟩⟩
  have h1 : sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x-f y‖/ρ x y} ≤ U := by
    apply csSup_le hn1
    rintro r ⟨i,j,hij,rfl⟩
    exact (div_le_iff₀ (hp i j hij)).mpr (hu i j)
  have h2 : sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y/‖f x-f y‖} ≤ V := by
    apply csSup_le hn2
    rintro r ⟨i,j,hij,rfl⟩
    exact (div_le_iff₀ (hn i j hij)).mpr (hv i j)
  have hnon : 0 ≤ sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y/‖f x-f y‖} :=
    (div_nonneg (hp x y hxy).le (norm_nonneg _)).trans
      (le_csSup (reverse_ratios_finite ρ f).bddAbove ⟨x,y,hxy,rfl⟩)
  unfold distortion
  exact mul_le_mul h1 h2 hnon hU

theorem leastDistortion_mono {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    [Nontrivial X] [Nontrivial Y] (ρX : X → X → ℝ) (ρY : Y → Y → ℝ)
    (hdX : ∀ x, ρX x x = 0) (hpX : ∀ x y, x ≠ y → 0 < ρX x y)
    (hdY : ∀ x, ρY x x = 0) (hpY : ∀ x y, x ≠ y → 0 < ρY x y)
    (e : X ↪ Y) (he : ∀ x y, ρY (e x) (e y) = ρX x y) :
    leastDistortion ρX ≤ leastDistortion ρY := by
  apply leastDistortion_lower
  intro f
  obtain ⟨U,V,hU,_,hD,hu,hv⟩ := distortion_constants ρY hdY hpY f
  let g : X ↪ L1 := e.trans f
  calc
    leastDistortion ρX ≤ distortion ρX g := leastDistortion_le ρX hdX hpX g
    _ ≤ U*V := distortion_le_of_bounds ρX hpX g hU.le
      (fun x y => by simpa only [g,Function.Embedding.trans_apply,he] using hu (e x) (e y))
      (fun x y => by simpa only [g,Function.Embedding.trans_apply,he] using hv (e x) (e y))
    _ = distortion ρY f := hD.symm

end EditDistortion

namespace EditDistortion
universe u

theorem binary_subset_lower (Alpha : Type u) [Fintype Alpha] (hAlpha : 2 ≤ Fintype.card Alpha)
    {d n : ℕ} (hn : n ≤ d) (S : Set (List Bool)) (hfin : S.Finite) (hnt : S.Nontrivial)
    (hlen : ∀ w ∈ S, w.length = n) :
    leastDistortion (fun x y : S => (edit x.val y.val : ℝ)) ≤ E Alpha d := by
  classical
  let : Fintype S := hfin.fintype
  let : Nontrivial S := hnt.coe_sort
  let : Finite (Words Alpha d) := finite_words Alpha d
  let : Fintype (Words Alpha d) := Fintype.ofFinite _
  let a : Bool ↪ Alpha := Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_bool] using hAlpha))
  let e : S ↪ Words Alpha d :=
    ⟨fun x => ⟨x.val.map a,by simpa only [List.length_map,hlen x.val x.property] using hn⟩,
      fun x y h => Subtype.ext ((List.map_inj_right a.injective).mp (congrArg Subtype.val h))⟩
  let : Nontrivial (Words Alpha d) := by
    obtain ⟨x,y,hxy⟩ := exists_pair_ne S
    exact ⟨⟨e x,e y,fun h => hxy (e.injective h)⟩⟩
  apply leastDistortion_mono _ _
    (fun x => edit_real_diag x.val)
    (fun x y hxy => edit_real_pos x.val y.val (fun h => hxy (Subtype.ext h)))
    (fun x => edit_real_diag x.val)
    (fun x y hxy => edit_real_pos x.val y.val (fun h => hxy (Subtype.ext h))) e
  intro x y
  exact_mod_cast cost_map_eq_of_leftInverse (s := true) a (Function.invFun a)
    (Function.leftInverse_invFun a.injective) x.val y.val

end EditDistortion

end OAI
