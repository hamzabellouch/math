import Mathlib
import OAI.Analysis.FreeWords.ConjugateFree

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ}

def laurentAlgebra (u : unitary A) : StarSubalgebra ℂ A :=
  StarAlgebra.adjoin ℂ {(u:A)}

def laurentSpan (u : unitary A) : Submodule ℂ A :=
  Submodule.span ℂ (Set.range (upow u))

def centeredLaurentSpan (u : unitary A) : Submodule ℂ A :=
  Submodule.span ℂ {x | ∃ k : ℤ, k ≠ 0 ∧ upow u k = x}

omit [PartialOrder A] [StarOrderedRing A] in
theorem upow_mem_laurentSpan (u : unitary A) (k : ℤ) :
    upow u k ∈ laurentSpan u := Submodule.subset_span ⟨k,rfl⟩

omit [PartialOrder A] [StarOrderedRing A] in
theorem laurentSpan_mul (u : unitary A) {x y : A}
    (hx : x ∈ laurentSpan u) (hy : y ∈ laurentSpan u) : x*y ∈ laurentSpan u := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l,rfl⟩ := hy
      rw [← upow_add]
      exact upow_mem_laurentSpan u _
    | zero => simp
    | add a b ha hb ia ib => simpa only [mul_add] using (laurentSpan u).add_mem ia ib
    | smul c a ha ia => simpa only [mul_smul_comm] using (laurentSpan u).smul_mem c ia
  | zero => simp
  | add a b ha hb ia ib => simpa only [add_mul] using (laurentSpan u).add_mem ia ib
  | smul c a ha ia => simpa only [smul_mul_assoc] using (laurentSpan u).smul_mem c ia

omit [PartialOrder A] [StarOrderedRing A] in
theorem laurentSpan_star (u : unitary A) {x : A} (hx : x ∈ laurentSpan u) :
    star x ∈ laurentSpan u := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k,rfl⟩ := hx
    rw [star_upow]
    exact upow_mem_laurentSpan u _
  | zero => simp
  | add a b ha hb ia ib => simpa only [star_add] using (laurentSpan u).add_mem ia ib
  | smul c a ha ia => simpa only [star_smul] using (laurentSpan u).smul_mem (star c) ia

omit [PartialOrder A] [StarOrderedRing A] in
theorem laurentAlgebra_le_span (u : unitary A) {x : A} (hx : x ∈ laurentAlgebra u) :
    x ∈ laurentSpan u := by
  induction hx using StarAlgebra.adjoin_induction with
  | mem x hx =>
    obtain rfl := Set.mem_singleton_iff.mp hx
    simpa using upow_mem_laurentSpan u 1
  | algebraMap c =>
    have h1 : (1:A) ∈ laurentSpan u := by simpa using upow_mem_laurentSpan u 0
    simpa [Algebra.algebraMap_eq_smul_one] using (laurentSpan u).smul_mem c h1
  | add x y hx hy ihx ihy => exact (laurentSpan u).add_mem ihx ihy
  | mul x y hx hy ihx ihy => exact laurentSpan_mul u ihx ihy
  | star x hx ih => exact laurentSpan_star u ih

omit [StarOrderedRing A] in
theorem centered_mem_laurentSpan (hτ : τ 1 = 1) (u : unitary A)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow u k) = 0)
    {x : A} (hx : x ∈ laurentSpan u) : x - τ x • 1 ∈ centeredLaurentSpan u := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k,rfl⟩ := hx
    by_cases hk : k=0
    · simp [hk,hτ]
    · rw [hHaar k hk,zero_smul,sub_zero]
      exact Submodule.subset_span ⟨k,hk,rfl⟩
  | zero => simp
  | add a b ha hb ia ib =>
    have he : a+b-τ (a+b) • (1:A) = (a-τ a • 1)+(b-τ b • 1) := by
      rw [map_add,add_smul]
      abel
    rw [he]
    exact (centeredLaurentSpan u).add_mem ia ib
  | smul c a ha ia =>
    rw [map_smul,smul_eq_mul,← smul_smul,← smul_sub]
    exact (centeredLaurentSpan u).smul_mem c ia

omit [StarOrderedRing A] in
theorem trace_zero_laurent_mem_span (hτ : τ 1 = 1) (u : unitary A)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow u k) = 0)
    {x : A} (hx : x ∈ laurentAlgebra u) (hz : τ x = 0) :
    x ∈ centeredLaurentSpan u := by
  simpa only [hz,zero_smul,sub_zero] using
    centered_mem_laurentSpan hτ u hHaar (laurentAlgebra_le_span u hx)

omit [PartialOrder A] [StarOrderedRing A] in
theorem linear_prod_zero_of_span {ι : Type*} (T : ι → Set A)
    (w : List (ι × A)) (φ : A →ₗ[ℂ] ℂ)
    (hw : ∀ a ∈ w, a.2 ∈ Submodule.span ℂ (T a.1))
    (hzero : ∀ y : List (ι × A), y.map Prod.fst = w.map Prod.fst →
      (∀ a ∈ y, a.2 ∈ T a.1) → φ ((y.map Prod.snd).prod) = 0) :
    φ ((w.map Prod.snd).prod) = 0 := by
  induction w generalizing φ with
  | nil => exact hzero [] rfl (by simp)
  | cons a w ih =>
    obtain ⟨i,x⟩ := a
    have htail : ∀ a ∈ w, a.2 ∈ Submodule.span ℂ (T a.1) :=
      fun a ha => hw a (List.mem_cons_of_mem _ ha)
    have hx := hw (i,x) (by simp)
    change x ∈ Submodule.span ℂ (T i) at hx
    simp only [List.map_cons] at hzero
    clear hw
    simp only [List.map_cons,List.prod_cons]
    induction hx using Submodule.span_induction with
    | mem x hx =>
      apply ih (φ.comp (LinearMap.mulLeft ℂ x)) htail
      intro y hy hmem
      simpa using hzero ((i,x)::y) (by simpa using hy) (by
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hx
        · exact hmem a ha)
    | zero => simp
    | add x z hx hz ix iz => simp only [add_mul,map_add,ix,iz,add_zero]
    | smul c x hx ix => simp only [smul_mul_assoc,map_smul,ix,smul_zero]

end

end KKFreeWords
end

end OAI
