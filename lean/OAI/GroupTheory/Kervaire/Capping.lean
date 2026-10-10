import OAI.GroupTheory.Kervaire.Splicing

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]

omit [Fintype D] in
lemma suppress_paired (θ : Perm D) {x y : D} (ht : θ x = y) :
    suppress θ x y = swap x y * θ := by
  simp only [suppress,ht,swap_self]
  change swap x y * (1 * θ * 1) = _
  simp only [one_mul,mul_one]

omit [Fintype D] in
lemma suppress_involutive_all (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hy : θ y ≠ y) :
    ∀ d, suppress θ x y (suppress θ x y d) = d := by
  by_cases ht : θ x = y
  · rw [suppress_paired θ ht]
    have hty : θ y = x := by simpa only [hθ] using (congrArg θ ht).symm
    intro d
    by_cases hd : d = x
    · subst d; simp only [mul_apply,ht,swap_apply_right]
    by_cases hd' : d = y
    · subst d; simp only [mul_apply,hty,swap_apply_left]
    have hdx : θ d ≠ x := fun h ↦ hd' (by simpa only [hθ,ht] using congrArg θ h)
    have hdy : θ d ≠ y := fun h ↦ hd (by simpa only [hθ,hty] using congrArg θ h)
    simp only [mul_apply,swap_apply_of_ne_of_ne hdx hdy,hθ,swap_apply_of_ne_of_ne hd hd']
  · exact suppress_involutive θ hθ hxy hx ht hy

omit [Fintype D] in
lemma suppress_fixed_all (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hy : θ y ≠ y) :
    suppress θ x y x = x ∧ suppress θ x y y = y := by
  by_cases ht : θ x = y
  · have hyx : θ y = x := by simpa only [hθ] using (congrArg θ ht).symm
    rw [suppress_paired θ ht]
    simp only [mul_apply,ht,hyx,swap_apply_left,swap_apply_right,and_self]
  · exact ⟨(suppress_apply θ hθ hxy hx ht hy).1,(suppress_apply θ hθ hxy hx ht hy).2.1⟩

def capSign (t : D → ℤ) (x y : D) (d : D) : ℤ := if d = x ∨ d = y then 0 else t d

omit [Fintype D] in
lemma capSign_other (t : D → ℤ) {x y d : D} (hdx : d ≠ x) (hdy : d ≠ y) :
    capSign t x y d = t d := ite_eq_right (not_or_intro hdx hdy)

omit [Fintype D] in
lemma suppress_sign (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (t : D → ℤ) (ht : ∀ d, t (θ d) = -t d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hy : θ y ≠ y) (hpair : t y = -t x) :
    ∀ d, capSign t x y (suppress θ x y d) = - capSign t x y d := by
  have hf := suppress_fixed_all θ hθ hxy hx hy
  intro d
  by_cases hdx : d = x
  · subst d; rw [hf.1]; simp [capSign]
  by_cases hdy : d = y
  · subst d; rw [hf.2]; simp [capSign]
  have htx : suppress θ x y d ≠ x := fun h ↦ hdx ((suppress θ x y).injective (h.trans hf.1.symm))
  have hty : suppress θ x y d ≠ y := fun h ↦ hdy ((suppress θ x y).injective (h.trans hf.2.symm))
  rw [capSign_other t htx hty,capSign_other t hdx hdy]
  by_cases htp : θ x = y
  · have hyt : θ y = x := by simpa only [hθ] using (congrArg θ htp).symm
    rw [suppress_paired θ htp,mul_apply,swap_apply_of_ne_of_ne]
    · exact ht d
    · exact fun h ↦ hdy (by simpa only [hθ,htp] using congrArg θ h)
    · exact fun h ↦ hdx (by simpa only [hθ,hyt] using congrArg θ h)
  · have hs := suppress_apply θ hθ hxy hx htp hy
    by_cases hdp : d = θ x
    · subst d; rw [hs.2.2.1,ht,ht,hpair]
    by_cases hdq : d = θ y
    · subst d; rw [hs.2.2.2,ht,ht,hpair]; omega
    rw [suppress_other θ hθ hdx hdy hdp hdq,ht]

omit [Fintype D] [Group A] in
lemma suppress_u_except (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    (u : D → A) {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hy : θ y ≠ y)
    (hup : u (θ x) = u y) {d : D} (hdx : d ≠ x) (hdy : d ≠ y) (hdp : d ≠ θ x) :
    u (suppress θ x y d) = u (θ d) := by
  by_cases ht : θ x = y
  · have hyt : θ y = x := by simpa only [hθ] using (congrArg θ ht).symm
    rw [suppress_paired θ ht,mul_apply,swap_apply_of_ne_of_ne]
    · exact fun h ↦ hdy (by simpa only [hθ,ht] using congrArg θ h)
    · exact fun h ↦ hdx (by simpa only [hθ,hyt] using congrArg θ h)
  · by_cases hdq : d = θ y
    · subst d; rw [(suppress_apply θ hθ hxy hx ht hy).2.2.2,hθ,hup]
    · rw [suppress_other θ hθ hdx hdy hdp hdq]
end

open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

/-- At a freely cancellable outside pair, the two remaining band endpoints
can be aligned without changing any corner. The same-face case is exactly
where the analytic planar-boundary theorem is needed. -/
theorem cap_alignment [Nonempty I]
    (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d) (t : D → ℤ)
    (ht : ∀ d, t (θ d) = -t d) (hp : planar σ θ)
    (b : DiskAtlas (V := V) ρ a s σ t) (u : D → A)
    (hu : ∀ v i, vertexCorner ρ a b.ε (v,i) = corner σ θ u (b.disk (v,i)))
    {x y : D} (hxy : x ≠ y) (hsx : σ x = y) (hsy : σ y ≠ x)
    (hx : θ x ≠ x) (hy : θ y ≠ y) (hpair : t y = -t x) (hcx : corner σ θ u x = 1)
    (hdisj : ∀ vi, ¬ σ.SameCycle (b.disk vi) x)
    (hcover : ∀ d, (∃ vi, b.disk vi = d) ∨ σ.SameCycle d x ∨ (σ d = d ∧ θ d = d)) :
    ∃ v : D → A, corner σ θ v = corner σ θ u ∧ v (θ y) = v x := by
  by_cases hface : (σ*θ).SameCycle x (θ y)
  swap
  · exact align_distinct_faces σ θ hθ u hface
  by_cases hpaired : θ x = y
  · have hyx : θ y = x := by simpa only [hθ] using (congrArg θ hpaired).symm
    exact ⟨u,rfl,congrArg u hyx⟩
  have hyx : θ y ≠ x := fun h ↦ hpaired (by simpa only [hθ] using (congrArg θ h).symm)
  have hzy : σ y ≠ y := fun h ↦ hxy (σ.injective (hsx.trans h.symm))
  let τ := swap x (σ y)*σ
  let σ' := erase (erase σ x) y
  let θ' := suppress θ x y
  let t' := capSign t x y
  have hcy : σ.SameCycle x (σ y) := (hsx ▸ SameCycle.rfl.apply_right).apply_right
  have hφ : (σ*θ).SameCycle x (σ y) := by simpa only [mul_apply,hθ] using hface.apply_right
  have hsep : ¬ components τ θ x (σ y) := planar_vertex_split_separates σ θ hsy.symm hcy hφ hp
  have hτx : τ x = y := by simp only [τ,mul_apply,hsx,swap_apply_of_ne_of_ne hxy.symm hzy.symm]
  have hrle : components σ' θ' ≤ components τ θ := by
    have hh := components_suppress τ θ hτx
    rw [← cap_vertex σ hxy hsx hsy] at hh
    exact ((le_joinPair _ _ _).trans (le_joinPair _ _ _)).trans_eq hh
  have hfix := suppress_apply θ hθ hxy hx hpaired hy
  have hs'x : σ' x = x := by
    dsimp only [σ']; rw [erase_apply _ _ _ hxy,erase_fixed,ite_eq_right hxy]
  have hs'y : σ' y = y := erase_fixed _ _
  have hpneq : θ x ≠ y := hpaired
  have houtside (d : D) (hd : σ.SameCycle d x) (hdx : d ≠ x) (hdy : d ≠ y) :
      σ'.SameCycle d (σ y) := by
    apply (sameCycle_erase (erase σ x) (x := y) (d := d) (e := σ y) (by
      rw [erase_apply _ _ _ hxy.symm,ite_eq_right hsy]; exact hzy) hdy hzy).mpr
    apply (sameCycle_erase σ (x := x) (d := d) (e := σ y) (by rw [hsx]; exact hxy.symm) hdx hsy).mpr
    exact hd.trans hcy
  have hcovered : ∀ d, components σ' θ' (θ x) d → ∃ vi, b.disk vi = d := by
    intro d hd
    rcases hcover d with h | h | h
    · exact h
    · have hdx : d ≠ x := fun he ↦ hx (components_eq_of_fixed σ' θ' hs'x hfix.1 ((components σ' θ').symm' (he ▸ hd))).symm
      have hdy : d ≠ y := fun he ↦ hpaired (components_eq_of_fixed σ' θ' hs'y hfix.2.1 ((components σ' θ').symm' (he ▸ hd))).symm
      apply False.elim
      apply hsep
      exact (components τ θ).trans' ((le_sup_right : SameCycle.setoid θ ≤ components τ θ) SameCycle.rfl.apply_right)
        (hrle ((components σ' θ').trans' hd ((le_sup_left : SameCycle.setoid σ' ≤ components σ' θ') (houtside d h hdx hdy))))
    · have hdx : d ≠ x := fun he ↦ hx (he ▸ h.2)
      have hdy : d ≠ y := fun he ↦ hy (he ▸ h.2)
      have hdp : d ≠ θ x := fun he ↦ hx (by simpa only [he,hθ] using h.2.symm)
      have hdq : d ≠ θ y := fun he ↦ hy (by simpa only [he,hθ] using h.2.symm)
      have hs'd : σ' d = d := by dsimp only [σ']; rw [cap_vertex_other σ hxy hsx hdx hdy,h.1,ite_eq_right hdx]
      have ht'd : θ' d = d := by dsimp only [θ']; rw [suppress_other θ hθ hdx hdy hdp hdq,h.2]
      exact False.elim (hdp (components_eq_of_fixed σ' θ' hs'd ht'd ((components σ' θ').symm' hd)))
  have disk_ne (vi : V × I) : b.disk vi ≠ x ∧ b.disk vi ≠ y := by
    constructor
    · exact fun h ↦ hdisj vi (h ▸ SameCycle.rfl)
    · intro h
      apply hdisj vi
      rw [h,← hsx]
      exact SameCycle.rfl.apply_left
  have disk_next (v : V) (i : I) : σ' (b.disk (v,i)) = σ (b.disk (v,i)) := by
    dsimp only [σ']; rw [cap_vertex_other σ hxy hsx (disk_ne _).1 (disk_ne _).2,ite_eq_right]
    rw [b.next]
    exact (disk_ne _).1
  let b' : DiskAtlas (V := V) ρ a s σ' t' := {
    disk := b.disk, ε := b.ε, polarity := b.polarity
    next := fun v i ↦ (disk_next v i).trans (b.next v i)
    sign := fun v i ↦ (capSign_other t (disk_ne _).1 (disk_ne _).2).trans (b.sign v i) }
  have hup : u (θ x) = u y := by
    apply mul_inv_eq_one.mp
    simpa only [corner,hsx] using hcx
  have hh := atlas_component_rigidity ρ hρ a s hs hsum σ' θ'
    (suppress_involutive θ hθ hxy hx hpaired hy) t'
    (suppress_sign θ hθ t ht hxy hx hy hpair) (planar_cap σ θ hθ hxy hsx hsy hx hy hp)
    b' u (θ x) hcovered (by
      intro v i hne
      change vertexCorner ρ a b.ε (v,i) = _
      rw [hu]
      simp only [corner]
      rw [disk_next,suppress_u_except θ hθ u hxy hx hy hup (disk_ne _).1 (disk_ne _).2 hne])
  obtain ⟨⟨v,i⟩,hvi⟩ := hcovered (θ x) ((components σ' θ').refl _)
  have heq := (hu v i).symm.trans (hh (v,i) hvi)
  rw [hvi] at heq
  change u (θ (θ x)) * (u (σ (θ x)))⁻¹ = u (θ' (θ x)) * (u (σ' (θ x)))⁻¹ at heq
  have hsp : σ' (θ x) = σ (θ x) := by simpa only [hvi] using disk_next v i
  rw [hsp,hθ,hfix.2.2.1] at heq
  exact ⟨u,rfl,(mul_right_cancel heq).symm⟩
end KervaireRibbon

end

end OAI
