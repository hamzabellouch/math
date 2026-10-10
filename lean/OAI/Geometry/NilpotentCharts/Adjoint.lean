import Mathlib

namespace OAI

/-! The adjoint action and nilpotence from differentiated group commutators. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawLieAdjoint
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] {G : Type} [Group G] [TopologicalSpace G]
  [ChartedSpace (E₀) G]
  [LieGroup (𝓘(ℝ, E₀)) ∞ G]
local notation "𝓘ₙ" => 𝓘(ℝ, E₀)
local notation "E" => E₀

 
def derivative (f : G → G) (x : G) : E →L[ℝ] E := mfderiv 𝓘ₙ 𝓘ₙ f x

lemma mul_derivative_one (v w : E) :
    mfderiv ((𝓘ₙ).prod 𝓘ₙ) 𝓘ₙ (fun p : G × G => p.1 * p.2) (1,1) (v,w) = v + w := by
  let D : (E × E) →L[ℝ] E :=
    mfderiv ((𝓘ₙ).prod 𝓘ₙ) 𝓘ₙ (fun p : G × G => p.1 * p.2) (1,1)
  have hm : MDifferentiableAt ((𝓘ₙ).prod 𝓘ₙ) 𝓘ₙ
      (fun p : G × G => p.1 * p.2) (1,1) :=
    (contMDiff_mul 𝓘ₙ 1).mdifferentiableAt one_ne_zero
  have hi : MDifferentiableAt 𝓘ₙ 𝓘ₙ (id : G → G) 1 := mdifferentiableAt_id
  have ho : MDifferentiableAt 𝓘ₙ 𝓘ₙ (fun _ : G => (1 : G)) 1 := mdifferentiableAt_const
  have hL : ∀ u : E, D (u,0) = u := by
    intro u
    have h := mfderiv_comp (I' := (𝓘ₙ).prod 𝓘ₙ) (f := fun g : G => (g,1)) (g := fun p : G × G => p.1 * p.2) (1 : G) hm (hi.prodMk ho)
    have he := congrArg (fun f : E →L[ℝ] E => f u) h
    have hid : (fun p : G × G => p.1 * p.2) ∘ (fun g : G => (g,1)) = id := by
      ext g; exact mul_one g
    have hp := mfderiv_prodMk hi ho
    change (mfderiv 𝓘ₙ ((𝓘ₙ).prod 𝓘ₙ) (fun g : G => (g,1)) 1 : E →L[ℝ] E × E) = _ at hp
    rw [mfderiv_id, mfderiv_const] at hp
    rw [hid, mfderiv_id, hp] at he
    exact he.symm
  have hR : ∀ u : E, D (0,u) = u := by
    intro u
    have h := mfderiv_comp (I' := (𝓘ₙ).prod 𝓘ₙ) (f := fun g : G => (1,g)) (g := fun p : G × G => p.1 * p.2) (1 : G) hm (ho.prodMk hi)
    have he := congrArg (fun f : E →L[ℝ] E => f u) h
    have hid : (fun p : G × G => p.1 * p.2) ∘ (fun g : G => (1,g)) = id := by
      ext g; exact one_mul g
    have hp := mfderiv_prodMk ho hi
    change (mfderiv 𝓘ₙ ((𝓘ₙ).prod 𝓘ₙ) (fun g : G => (1,g)) 1 : E →L[ℝ] E × E) = _ at hp
    rw [mfderiv_const, mfderiv_id] at hp
    rw [hid, mfderiv_id, hp] at he
    exact he.symm
  change D (v,w) = v+w
  rw [show (v,w) = (v,0) + (0,w) by simp, map_add, hL, hR]

lemma product_derivative_one {f g : G → G} (hf0 : f 1 = 1) (hg0 : g 1 = 1)
    (hf : MDifferentiableAt 𝓘ₙ 𝓘ₙ f 1) (hg : MDifferentiableAt 𝓘ₙ 𝓘ₙ g 1) :
    derivative (E₀ := E₀) (fun x => f x * g x) 1 = derivative (E₀ := E₀) f 1 + derivative (E₀ := E₀) g 1 := by
  have hm : MDifferentiableAt ((𝓘ₙ).prod 𝓘ₙ) 𝓘ₙ
      (fun p : G × G => p.1 * p.2) (f 1,g 1) :=
    (contMDiff_mul 𝓘ₙ 1).mdifferentiableAt one_ne_zero
  have h := mfderiv_comp (I' := (𝓘ₙ).prod 𝓘ₙ) (f := fun x => (f x,g x)) (g := fun p : G × G => p.1*p.2) (1 : G) hm (hf.prodMk hg)
  have hp := mfderiv_congr_point (I := (𝓘ₙ).prod 𝓘ₙ) (I' := 𝓘ₙ)
    (f := fun p : G × G => p.1 * p.2) (show (f 1,g 1) = (1,1) by rw [hf0,hg0])
  apply ContinuousLinearMap.ext
  intro u
  have he := congrArg (fun D : E →L[ℝ] E => D u) h
  rw [mfderiv_prodMk hf hg, hp] at he
  change (mfderiv 𝓘ₙ 𝓘ₙ (fun x => f x*g x) 1) u = _ at he
  exact he.trans (mul_derivative_one _ _)

lemma inv_derivative_one :
    derivative (E₀ := E₀) (fun g : G => g⁻¹) 1 =
      -ContinuousLinearMap.id ℝ E := by
  have hid : MDifferentiableAt 𝓘ₙ 𝓘ₙ (id : G → G) 1 := mdifferentiableAt_id
  have hinv : MDifferentiableAt 𝓘ₙ 𝓘ₙ (fun g : G => g⁻¹) 1 :=
    (contMDiff_inv (I := 𝓘ₙ) (n := 1)).mdifferentiableAt one_ne_zero
  have h := product_derivative_one (E₀ := E₀) (G := G) rfl (inv_one) hid hinv
  have hh : (fun g : G => g * g⁻¹) = (fun _ => 1) := funext mul_inv_cancel
  have hzero : derivative (E₀ := E₀) (fun g : G => g * g⁻¹) 1 = 0 :=
    (mfderiv_congr (I := 𝓘ₙ) (I' := 𝓘ₙ) (x := (1 : G)) hh).trans mfderiv_const
  have hid' : derivative (E₀ := E₀) (id : G → G) 1 = ContinuousLinearMap.id ℝ E :=
    mfderiv_id
  change derivative (E₀ := E₀) (fun g : G => g * g⁻¹) 1 = _ at h
  rw [hzero, hid'] at h
  exact eq_neg_of_add_eq_zero_right h.symm

omit [LieGroup 𝓘(ℝ, E₀) ∞ G] in
lemma derivative_comp_one {f g : G → G} (hf0 : f 1 = 1)
    (hf : MDifferentiableAt 𝓘ₙ 𝓘ₙ f 1) (hg : MDifferentiableAt 𝓘ₙ 𝓘ₙ g 1) :
    derivative (E₀ := E₀) (g ∘ f) 1 =
      (derivative (E₀ := E₀) g 1).comp (derivative (E₀ := E₀) f 1) := by
  have hg' : MDifferentiableAt 𝓘ₙ 𝓘ₙ g (f 1) := hf0.symm ▸ hg
  have hc := mfderiv_comp (I' := 𝓘ₙ) (f := f) (g := g) (1 : G) hg' hf
  have hp := mfderiv_congr_point (I := 𝓘ₙ) (I' := 𝓘ₙ) (f := g) hf0
  exact hc.trans (congrArg (fun D : E →L[ℝ] E => D.comp (derivative (E₀ := E₀) f 1)) hp)

open scoped commutatorElement

def commMap (g h : G) : G := ⁅h,g⁆

omit [TopologicalSpace G] in
@[simp] lemma commMap_one (g : G) : commMap g 1 = 1 := commutatorElement_one_left g

lemma commMap_smooth (g : G) : ContMDiff 𝓘ₙ 𝓘ₙ 1 (commMap g) := by
  unfold commMap
  simp only [commutatorElement_def]
  exact ((contMDiff_id.mul contMDiff_const).mul (contMDiff_inv (I := 𝓘ₙ) (n := 1))).mul
    contMDiff_const

def iterComm : List G → G → G
  | [] => id
  | g :: l => commMap g ∘ iterComm l

omit [TopologicalSpace G] in
@[simp] lemma iterComm_one (l : List G) : iterComm l 1 = 1 := by
  induction l with
  | nil => rfl
  | cons g l ih => simp [iterComm, ih]

lemma iterComm_smooth (l : List G) : ContMDiff 𝓘ₙ 𝓘ₙ 1 (iterComm l) := by
  induction l with
  | nil => exact contMDiff_id
  | cons g l ih => exact (commMap_smooth (E₀ := E₀) g).comp ih

omit [TopologicalSpace G] in
lemma iterComm_mem (l : List G) (h : G) :
    iterComm l h ∈ (⊤ : Subgroup G).lowerCentralSeries l.length := by
  induction l with
  | nil => trivial
  | cons g l ih => exact Subgroup.commutator_mem_commutator ih (Subgroup.mem_top g)

lemma iterComm_derivative (l : List G) :
    derivative (E₀ := E₀) (iterComm l) 1 = (l.map (fun g => derivative (E₀ := E₀) (commMap g) 1)).prod := by
  induction l with
  | nil => exact mfderiv_id
  | cons g l ih =>
    change derivative (E₀ := E₀) (commMap g ∘ iterComm l) 1 = _
    rw [derivative_comp_one (iterComm_one l)
      ((iterComm_smooth (E₀ := E₀) l).mdifferentiableAt one_ne_zero)
      ((commMap_smooth (E₀ := E₀) g).mdifferentiableAt one_ne_zero), ih]
    rfl

lemma nilpotent_mixed_derivative {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) (l : List G) (hl : l.length = s) :
    (l.map (fun g => derivative (E₀ := E₀) (commMap g) 1)).prod = 0 := by
  have he : iterComm l = fun _ => (1 : G) := by
    funext h
    have hm := iterComm_mem l h
    rw [hl, hstop, Subgroup.mem_bot] at hm
    exact hm
  rw [← iterComm_derivative]
  exact (mfderiv_congr (I := 𝓘ₙ) (I' := 𝓘ₙ) (x := (1 : G)) he).trans mfderiv_const

 

lemma exists_common_kernel {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : ι → V →L[ℝ] V) (s : ℕ) (v : V) (hv : v ≠ 0)
    (h : ∀ l : List ι, l.length = s → (l.map A).prod v = 0) :
    ∃ w : V, w ≠ 0 ∧ ∀ i, A i w = 0 := by
  induction s generalizing v with
  | zero =>
    have hz := h [] rfl
    simp only [List.map_nil, List.prod_nil, one_apply_eq_self] at hz
    exact (hv hz).elim
  | succ s ih =>
    by_cases hker : ∀ i, A i v = 0
    · exact ⟨v, hv, hker⟩
    · push Not at hker
      obtain ⟨i, hi⟩ := hker
      apply ih (A i v) hi
      intro l hl
      have hz := h (l ++ [i]) (by simp [hl])
      simpa only [List.map_append, List.map_cons, List.map_nil, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one, mul_apply_eq_comp] using hz

lemma conjugation_smooth (g : G) : ContMDiff 𝓘ₙ 𝓘ₙ 1 (MulAut.conj g : G → G) :=
  (contMDiff_const.mul contMDiff_id).mul contMDiff_const

 
def adjoint (g : G) : E →L[ℝ] E := derivative (E₀ := E₀) (MulAut.conj g) 1

lemma commMap_add_adjoint (g : G) :
    derivative (E₀ := E₀) (commMap g) 1 + adjoint (E₀ := E₀) g = ContinuousLinearMap.id ℝ E := by
  have h := product_derivative_one (commMap_one g) (map_one (MulAut.conj g))
    ((commMap_smooth (E₀ := E₀) g).mdifferentiableAt one_ne_zero)
    ((conjugation_smooth (E₀ := E₀) g).mdifferentiableAt one_ne_zero)
  have he : (fun h : G => commMap g h * MulAut.conj g h) = id := by
    funext h
    simp [commMap, commutatorElement_def, MulAut.conj_apply, mul_assoc]
  have hc := congrArg (fun f : G → G => derivative (E₀ := E₀) f 1) he
  rw [h] at hc
  exact hc.trans mfderiv_id

 

theorem exists_commutator_kernel {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) (v : E) (hv : v ≠ 0) :
    ∃ w : E, w ≠ 0 ∧ ∀ g : G, derivative (E₀ := E₀) (commMap g) 1 w = 0 := by
  apply exists_common_kernel (fun g : G => derivative (E₀ := E₀) (commMap g) 1) s v hv
  intro l hl
  rw [nilpotent_mixed_derivative hstop l hl]
  rfl

theorem exists_adjoint_fixed {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) (v : E) (hv : v ≠ 0) :
    ∃ w : E, w ≠ 0 ∧ ∀ g : G, adjoint (E₀ := E₀) g w = w := by
  obtain ⟨w, hw, hker⟩ := exists_commutator_kernel hstop v hv
  refine ⟨w, hw, fun g => ?_⟩
  have h := congrArg (fun A : E →L[ℝ] E => A w) (commMap_add_adjoint (E₀ := E₀) g)
  simpa only [add_apply, hker g, zero_add, ContinuousLinearMap.id_apply] using h

end RawLieAdjoint
end

end OAI
