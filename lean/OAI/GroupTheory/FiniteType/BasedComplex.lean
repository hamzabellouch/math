import Mathlib

namespace OAI

noncomputable section
namespace BasedComplex

structure Data (B : Type*) where
  degree : B → ℕ
  d : (B →₀ ℤ) →ₗ[ℤ] (B →₀ ℤ)
  aug : (B →₀ ℤ) →ₗ[ℤ] ℤ
  d_squared : ∀ c, d (d c) = 0
  lowers : ∀ b t, t ∈ (d (Finsupp.single b 1)).support → degree t + 1 = degree b
  aug_single : ∀ b, aug (Finsupp.single b 1) = if degree b = 0 then 1 else 0
  aug_d : ∀ c, aug (d c) = 0

variable {B : Type*} (C : Data B)

lemma d_vertex {b : B} (hb : C.degree b = 0) : C.d (Finsupp.single b 1) = 0 := by
  classical
  apply Finsupp.support_eq_empty.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have H := C.lowers b t ht
  omega

lemma linear_eq_on_support {M : Type*} [AddCommGroup M]
    (f g : (B →₀ ℤ) →ₗ[ℤ] M) (c : B →₀ ℤ)
    (h : ∀ b ∈ c.support, f (Finsupp.single b 1) = g (Finsupp.single b 1)) : f c = g c := by
  classical
  conv_lhs => rw [← Finsupp.sum_single c]
  conv_rhs => rw [← Finsupp.sum_single c]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have he : Finsupp.single b (c b) = (c b) • Finsupp.single b 1 := by simp
  rw [he, LinearMap.map_smul, LinearMap.map_smul, h b hb]

structure Contraction {M : Type*} [AddCommGroup M]
    (d : M →ₗ[ℤ] M) (aug : M →ₗ[ℤ] ℤ) where
  point : M
  cone : M →ₗ[ℤ] M
  d_point : d point = 0
  aug_point : aug point = 1
  aug_cone : ∀ c, aug (cone c) = 0
  identity : ∀ c, d (cone c) + cone (d c) = c - aug c • point

variable {M : Type*} [AddCommGroup M]
  (d : M →ₗ[ℤ] M) (aug : M →ₗ[ℤ] ℤ) (T : B → Contraction d aug)

private def extendBasis (b : B) : M :=
  if C.degree b = 0 then (T b).point else
    (T b).cone (∑ t ∈ (C.d (Finsupp.single b 1)).support.attach,
      C.d (Finsupp.single b 1) t.1 • extendBasis t.1)
termination_by C.degree b
decreasing_by
  have h := C.lowers b t.1 t.2
  omega

def extend : (B →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (extendBasis C d aug T)

@[simp] lemma extend_single (b : B) :
    extend C d aug T (Finsupp.single b 1) = extendBasis C d aug T b := by
  simp only [extend, Finsupp.linearCombination_single, one_smul]

lemma extend_vertex {b : B} (hb : C.degree b = 0) :
    extend C d aug T (Finsupp.single b 1) = (T b).point := by
  rw [extend_single, extendBasis, ite_eq_left hb]

lemma extend_positive {b : B} (hb : C.degree b ≠ 0) :
    extend C d aug T (Finsupp.single b 1) =
      (T b).cone (extend C d aug T (C.d (Finsupp.single b 1))) := by
  rw [extend_single, extendBasis, ite_eq_right hb]
  congr 1
  simp only [extend, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_attach (C.d (Finsupp.single b 1)).support
    (fun t : B => (C.d (Finsupp.single b 1)) t • extendBasis C d aug T t)

lemma aug_extend (c : B →₀ ℤ) : aug (extend C d aug T c) = C.aug c := by
  have h : aug ∘ₗ extend C d aug T = C.aug := by
    apply Finsupp.lhom_ext
    intro b r
    have hr : Finsupp.single b r = r • Finsupp.single b 1 := by simp
    simp only [LinearMap.comp_apply, hr, LinearMap.map_smul]
    congr 1
    rw [C.aug_single]
    by_cases hb : C.degree b = 0
    · rw [extend_vertex C d aug T hb, (T b).aug_point, ite_eq_left hb]
    · rw [extend_positive C d aug T hb, (T b).aug_cone, ite_eq_right hb]
  exact LinearMap.congr_fun h c

theorem d_extend (c : B →₀ ℤ) : d (extend C d aug T c) = extend C d aug T (C.d c) := by
  have hb (n : ℕ) (b : B) (hn : C.degree b = n) :
      d (extend C d aug T (Finsupp.single b 1)) =
        extend C d aug T (C.d (Finsupp.single b 1)) := by
    induction n using Nat.strong_induction_on generalizing b with
    | h n ih =>
      by_cases hz : C.degree b = 0
      · rw [extend_vertex C d aug T hz, (T b).d_point, d_vertex C hz, map_zero]
      · rw [extend_positive C d aug T hz]
        have hc : d (extend C d aug T (C.d (Finsupp.single b 1))) = 0 := by
          have he := linear_eq_on_support (d ∘ₗ extend C d aug T)
            (extend C d aug T ∘ₗ C.d) (C.d (Finsupp.single b 1)) (by
              intro t ht
              have hd := C.lowers b t ht
              exact ih (C.degree t) (by omega) t rfl)
          simpa only [LinearMap.comp_apply, C.d_squared, map_zero] using he
        have he := (T b).identity (extend C d aug T (C.d (Finsupp.single b 1)))
        simpa only [hc, map_zero, add_zero, aug_extend, C.aug_d, zero_smul, sub_zero] using he
  have h : d ∘ₗ extend C d aug T = extend C d aug T ∘ₗ C.d := by
    apply Finsupp.lhom_ext
    intro b r
    have hr : Finsupp.single b r = r • Finsupp.single b 1 := by simp
    simp only [LinearMap.comp_apply, hr, LinearMap.map_smul, hb (C.degree b) b rfl]
  exact LinearMap.congr_fun h c

lemma map_mem_of_support {N : Type*} [AddCommGroup N]
    (f : (B →₀ ℤ) →ₗ[ℤ] N) (K : Submodule ℤ N) (c : B →₀ ℤ)
    (h : ∀ b ∈ c.support, f (Finsupp.single b 1) ∈ K) : f c ∈ K := by
  classical
  rw [← Finsupp.sum_single c, Finsupp.sum, map_sum]
  apply Submodule.sum_mem
  intro b hb
  have he : Finsupp.single b (c b) = (c b) • Finsupp.single b 1 := by simp
  rw [he, LinearMap.map_smul]
  exact K.smul_mem _ (h b hb)

theorem extend_mem (K : B → Submodule ℤ M)
    (hpoint : ∀ b, C.degree b = 0 → (T b).point ∈ K b)
    (hcone : ∀ b c, c ∈ K b → (T b).cone c ∈ K b)
    (hface : ∀ b t, t ∈ (C.d (Finsupp.single b 1)).support → K t ≤ K b)
    (b : B) : extend C d aug T (Finsupp.single b 1) ∈ K b := by
  suffices ∀ n b, C.degree b = n → extend C d aug T (Finsupp.single b 1) ∈ K b by
    exact this (C.degree b) b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b hn
    by_cases hz : C.degree b = 0
    · rw [extend_vertex C d aug T hz]
      exact hpoint b hz
    · rw [extend_positive C d aug T hz]
      apply hcone
      apply map_mem_of_support
      intro t ht
      apply hface b t ht
      apply ih (C.degree t) _ t rfl
      have hd := C.lowers b t ht
      omega

theorem extend_degree (D : ℕ → Submodule ℤ M)
    (hpoint : ∀ b, C.degree b = 0 → (T b).point ∈ D 0)
    (hcone : ∀ b n c, c ∈ D n → (T b).cone c ∈ D (n+1))
    (b : B) : extend C d aug T (Finsupp.single b 1) ∈ D (C.degree b) := by
  suffices ∀ n b, C.degree b = n → extend C d aug T (Finsupp.single b 1) ∈ D n by
    exact this (C.degree b) b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b hn
    by_cases hz : C.degree b = 0
    · rw [extend_vertex C d aug T hz, ← hn, hz]
      exact hpoint b hz
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hz
      have he : n = m+1 := by omega
      rw [extend_positive C d aug T hz, he]
      apply hcone
      apply map_mem_of_support
      intro t ht
      have hd := C.lowers b t ht
      have htdeg : C.degree t = m := by omega
      exact ih m (by omega) t htdeg

variable (F G : (B →₀ ℤ) →ₗ[ℤ] M)

private def homotopyBasis (b : B) : M :=
  (T b).cone (F (Finsupp.single b 1) - G (Finsupp.single b 1) -
    ∑ t ∈ (C.d (Finsupp.single b 1)).support.attach,
      C.d (Finsupp.single b 1) t.1 • homotopyBasis t.1)
termination_by C.degree b
decreasing_by
  have h := C.lowers b t.1 t.2
  omega

def homotopy : (B →₀ ℤ) →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (homotopyBasis C d aug T F G)

lemma homotopy_equation (b : B) :
    homotopy C d aug T F G (Finsupp.single b 1) =
      (T b).cone (F (Finsupp.single b 1) - G (Finsupp.single b 1) -
        homotopy C d aug T F G (C.d (Finsupp.single b 1))) := by
  rw [homotopy, Finsupp.linearCombination_single, one_smul, homotopyBasis]
  congr 2
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_attach (C.d (Finsupp.single b 1)).support
    (fun t : B => (C.d (Finsupp.single b 1)) t • homotopyBasis C d aug T F G t)

lemma aug_homotopy (c : B →₀ ℤ) : aug (homotopy C d aug T F G c) = 0 := by
  have he : aug ∘ₗ homotopy C d aug T F G = 0 := by
    apply Finsupp.lhom_ext
    intro b r
    have hr : Finsupp.single b r = r • Finsupp.single b 1 := by simp
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, hr, LinearMap.map_smul,
      homotopy_equation, (T b).aug_cone, smul_zero]
  exact LinearMap.congr_fun he c

theorem d_homotopy
    (hF : ∀ c, d (F c) = F (C.d c))
    (hG : ∀ c, d (G c) = G (C.d c))
    (haug : ∀ c, aug (F c) = aug (G c)) (c : B →₀ ℤ) :
    d (homotopy C d aug T F G c) + homotopy C d aug T F G (C.d c) = F c - G c := by
  have hb (n : ℕ) (b : B) (hn : C.degree b = n) :
      d (homotopy C d aug T F G (Finsupp.single b 1)) +
        homotopy C d aug T F G (C.d (Finsupp.single b 1)) =
        F (Finsupp.single b 1) - G (Finsupp.single b 1) := by
    induction n using Nat.strong_induction_on generalizing b with
    | h n ih =>
      have hdH : d (homotopy C d aug T F G (C.d (Finsupp.single b 1))) =
          F (C.d (Finsupp.single b 1)) - G (C.d (Finsupp.single b 1)) := by
        have he := linear_eq_on_support
          (d ∘ₗ homotopy C d aug T F G + homotopy C d aug T F G ∘ₗ C.d)
          (F - G) (C.d (Finsupp.single b 1)) (by
            intro t ht
            have hd := C.lowers b t ht
            exact ih (C.degree t) (by omega) t rfl)
        simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
          C.d_squared, map_zero, add_zero] using he
      have hcycle : d (F (Finsupp.single b 1) - G (Finsupp.single b 1) -
          homotopy C d aug T F G (C.d (Finsupp.single b 1))) = 0 := by
        rw [map_sub, map_sub, hF, hG, hdH, sub_self]
      have hzero : aug (F (Finsupp.single b 1) - G (Finsupp.single b 1) -
          homotopy C d aug T F G (C.d (Finsupp.single b 1))) = 0 := by
        rw [map_sub, map_sub, haug, sub_self, aug_homotopy, sub_self]
      have he := (T b).identity (F (Finsupp.single b 1) - G (Finsupp.single b 1) -
          homotopy C d aug T F G (C.d (Finsupp.single b 1)))
      rw [hcycle, map_zero, add_zero, hzero, zero_smul, sub_zero] at he
      rw [homotopy_equation, he]
      abel
  have he : d ∘ₗ homotopy C d aug T F G + homotopy C d aug T F G ∘ₗ C.d = F - G := by
    apply Finsupp.lhom_ext
    intro b r
    have hr : Finsupp.single b r = r • Finsupp.single b 1 := by simp
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      hr, LinearMap.map_smul, ← smul_add, ← smul_sub, hb (C.degree b) b rfl]
  exact LinearMap.congr_fun he c

lemma homotopy_mem (K : B → Submodule ℤ M)
    (hF : ∀ b, F (Finsupp.single b 1) ∈ K b)
    (hG : ∀ b, G (Finsupp.single b 1) ∈ K b)
    (hcone : ∀ b c, c ∈ K b → (T b).cone c ∈ K b)
    (hface : ∀ b t, t ∈ (C.d (Finsupp.single b 1)).support → K t ≤ K b)
    (b : B) : homotopy C d aug T F G (Finsupp.single b 1) ∈ K b := by
  suffices ∀ n b, C.degree b = n → homotopy C d aug T F G (Finsupp.single b 1) ∈ K b by
    exact this (C.degree b) b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b hn
    rw [homotopy_equation]
    apply hcone
    apply (K b).sub_mem ((K b).sub_mem (hF b) (hG b))
    apply map_mem_of_support
    intro t ht
    apply hface b t ht
    apply ih (C.degree t) _ t rfl
    have hd := C.lowers b t ht
    omega

theorem homotopy_degree (D : ℕ → Submodule ℤ M)
    (hF : ∀ b, F (Finsupp.single b 1) ∈ D (C.degree b))
    (hG : ∀ b, G (Finsupp.single b 1) ∈ D (C.degree b))
    (hcone : ∀ b n c, c ∈ D n → (T b).cone c ∈ D (n+1))
    (b : B) : homotopy C d aug T F G (Finsupp.single b 1) ∈ D (C.degree b + 1) := by
  suffices ∀ n b, C.degree b = n →
      homotopy C d aug T F G (Finsupp.single b 1) ∈ D (n+1) by
    exact this (C.degree b) b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b hn
    rw [homotopy_equation]
    apply hcone
    apply (D n).sub_mem
    · exact (D n).sub_mem (hn ▸ hF b) (hn ▸ hG b)
    · apply map_mem_of_support
      intro t ht
      have hd := C.lowers b t ht
      have he : C.degree t + 1 = n := by omega
      rw [← he]
      exact ih (C.degree t) (by omega) t rfl

end BasedComplex

end

end OAI
