import OAI.Analysis.BoundedHochschild.FiniteGroupCochainAverages

namespace OAI

/-! The module identities of the contractive finite-group cochain average. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u v
variable {M : Type u} [CStarAlgebra M]

lemma cochainUnitaryTransport_fixed_value {n : ℕ} (u : Fin (n + 1) → unitary M)
    (f : Cochain M n) (hf : cochainUnitaryTransport u f = f) (x : Fin n → M) :
    f (cochainUnitaryTuple u x) = (u 0 : M) * f x * star (u (Fin.last n) : M) := by
  have h := congrArg (fun F : Cochain M n => (u 0 : M) * F x * star (u (Fin.last n) : M)) hf
  simp only [cochainUnitaryTransport_apply, mul_assoc,
    Unitary.mul_star_self_of_mem (u (Fin.last n)).property, mul_one] at h
  rw [← mul_assoc, Unitary.mul_star_self_of_mem (u 0).property, one_mul] at h
  simpa only [mul_assoc] using h

lemma cochainUnitaryTuple_left {n : ℕ} (u : unitary M) (x : Fin (n + 1) → M) :
    cochainUnitaryTuple (Function.update (fun _ : Fin (n + 2) => 1) 0 u) x =
      Function.update x 0 ((u : M) * x 0) := by
  ext i
  by_cases hi : i = 0
  · subst i
    simp [cochainUnitaryTuple]
  · have hi0 : i.castSucc ≠ (0 : Fin (n + 2)) := by
      intro h
      exact hi (Fin.ext (congrArg (fun z : Fin (n + 2) => z.val) h))
    simp [cochainUnitaryTuple, hi, hi0]

lemma cochainUnitaryTuple_right {n : ℕ} (u : unitary M) (x : Fin (n + 1) → M) :
    cochainUnitaryTuple (Function.update (fun _ : Fin (n + 2) => 1) (Fin.last (n + 1)) u) x =
      Function.update x (Fin.last n) (x (Fin.last n) * star (u : M)) := by
  ext i
  by_cases hi : i = Fin.last n
  · subst i
    simp [cochainUnitaryTuple]
  · have hiL : i.succ ≠ Fin.last (n + 1) := by
      intro h
      apply hi
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_last] at hv ⊢
      omega
    simp [cochainUnitaryTuple, hi, hiL]

lemma cochainUnitaryTuple_internal {n : ℕ} (u : unitary M) (x : Fin (n + 1) → M) (j : Fin n) :
    cochainUnitaryTuple (Function.update (fun _ : Fin (n + 2) => 1) j.castSucc.succ u) x =
      Function.update (Function.update x j.castSucc (x j.castSucc * star (u : M)))
        j.succ ((u : M) * x j.succ) := by
  have hjs : j.castSucc ≠ j.succ := ne_of_lt Fin.castSucc_lt_succ
  ext i
  by_cases hi : i = j.castSucc
  · subst i
    have hne : j.castSucc.castSucc ≠ j.castSucc.succ := ne_of_lt Fin.castSucc_lt_succ
    simp only [cochainUnitaryTuple, Function.update_of_ne hne, Function.update_self,
      Function.update_of_ne hjs, OneMemClass.coe_one, one_mul]
  · by_cases hi' : i = j.succ
    · subst i
      have hne : j.succ.succ ≠ j.castSucc.succ := by
        simpa only [ne_eq, Fin.succ_inj] using hjs.symm
      have heq : j.succ.castSucc = j.castSucc.succ := Fin.castSucc_succ j
      simp only [cochainUnitaryTuple, heq, Function.update_self, Function.update_of_ne hne,
        OneMemClass.coe_one, star_one, mul_one]
    · have hneL : i.castSucc ≠ j.castSucc.succ := by
        simpa only [← Fin.castSucc_succ, ne_eq, Fin.castSucc_inj] using hi'
      have hneR : i.succ ≠ j.castSucc.succ := by
        simpa only [ne_eq, Fin.succ_inj] using hi
      simp only [cochainUnitaryTuple, Function.update_of_ne hneL, Function.update_of_ne hneR,
        Function.update_of_ne hi, Function.update_of_ne hi', OneMemClass.coe_one,
        star_one, one_mul, mul_one]

variable {G : Type v} [Group G] [Fintype G]

lemma finiteGroupCochainAverage_multimodularAt {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) (g : G) :
    MultimodularAt (finiteGroupCochainAverage ρ f) (ρ g : M) := by
  let F := finiteGroupCochainAverage ρ f
  have hvalue (h : Fin (n + 2) → G) (x : Fin (n + 1) → M) :
      F (cochainUnitaryTuple (fun i => ρ (h i)) x) =
        (ρ (h 0) : M) * F x * star (ρ (h (Fin.last (n + 1))) : M) :=
    cochainUnitaryTransport_fixed_value _ F (finiteGroupCochainAverage_invariant ρ f h) x
  have hρ (i : Fin (n + 2)) (h : G) :
      (fun k => ρ (Function.update (fun _ : Fin (n + 2) => (1 : G)) i h k)) =
        Function.update (fun _ : Fin (n + 2) => 1) i (ρ h) := by
    ext k
    by_cases hk : k = i <;> simp [hk]
  constructor
  · intro x
    have h := hvalue (Function.update (fun _ => 1) 0 g) x
    rw [hρ, cochainUnitaryTuple_left] at h
    simpa using h
  · intro x
    have h := hvalue (Function.update (fun _ => 1) (Fin.last (n + 1)) g⁻¹) x
    rw [hρ, cochainUnitaryTuple_right] at h
    have hu : star (ρ g⁻¹ : M) = (ρ g : M) := by
      rw [map_inv]
      change star (star (ρ g : M)) = (ρ g : M)
      exact star_star _
    simpa only [Function.update_self, map_one, OneMemClass.coe_one, one_mul,
      Function.update_of_ne (by simp : (0 : Fin (n + 2)) ≠ Fin.last (n + 1)), hu] using h
  · intro x j
    let y := Function.update x j.castSucc (x j.castSucc * (ρ g : M))
    have h := hvalue (Function.update (fun _ => 1) j.castSucc.succ g) y
    rw [hρ, cochainUnitaryTuple_internal] at h
    have hz : Function.update
        (Function.update y j.castSucc (y j.castSucc * star (ρ g : M)))
        j.succ ((ρ g : M) * y j.succ) =
        Function.update x j.succ ((ρ g : M) * x j.succ) := by
      have hu := Unitary.mul_star_self_of_mem (ρ g).property
      simp only [y, Function.update_self, mul_assoc, hu, mul_one,
        Function.update_idem, Function.update_eq_self]
      simp [ne_of_gt (Fin.castSucc_lt_succ (i := j))]
    rw [hz] at h
    have hfirst : (0 : Fin (n + 2)) ≠ j.castSucc.succ := by
      intro hh
      have hv := congrArg Fin.val hh
      simp at hv
    have hlast : Fin.last (n + 1) ≠ j.castSucc.succ := by
      exact Ne.symm (ne_of_lt (Fin.castSucc_lt_last j.succ))
    simpa only [Function.update_of_ne hfirst, Function.update_of_ne hlast,
      map_one, OneMemClass.coe_one, star_one, one_mul, mul_one] using h.symm

lemma finiteGroupCochainAverage_span {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) {a : M}
    (ha : a ∈ Submodule.span ℂ (Set.range (fun g => (ρ g : M)))) :
    MultimodularAt (finiteGroupCochainAverage ρ f) a := by
  apply multimodularAt_of_span _ _ _ ha
  rintro _ ⟨g, rfl⟩
  exact finiteGroupCochainAverage_multimodularAt ρ f g

end BoundedHochschild.KadisonRingrose

end

end OAI
