import Mathlib
import OAI.Geometry.Cannon.Energy.RawFunction
import OAI.Geometry.Cannon.Energy.StripCrossing
import OAI.Geometry.Cannon.Modulus.ModulusEnergy

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval
open Set Metric Topology
open Set Topology unitInterval

namespace CannonCharts

open CannonCells

theorem rectangle_modulus_localization {X : Type*} [MetricSpace X] [CompactSpace X]
    (φ : X ≃ₜ SphereTwo) (d : ℝ) (hd : 0 < d)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)]
    (C : (n : ℕ) → ι n → Set X) (hC : ∀ n x, ∃ i, x ∈ C n i) :
    ∃ e : Plane → X, IsOpenEmbedding e ∧ diam (e '' box 8) < d ∧
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ → ℕ, StrictMono N ∧ ∀ n,
        c * modulus (C (N n)) (macroFamily (X := X) d) ≤
          modulus (C (N n)) (stripFamily e) := by
  classical
  obtain ⟨J,e,hJ,he,hdiam,hsub⟩ := finite_strip_localization φ d hd
  let : Nonempty J := hJ.coe_sort
  let H := fun j : J × Fin 4 => stripFamily (e j)
  let K : ℝ := (Fintype.card (J × Fin 4) : ℝ)^2
  have hK : 0 < K := pow_pos (by exact_mod_cast Fintype.card_pos) _
  have hlocal (n : ℕ) : ∃ j : J × Fin 4,
      modulus (C n) (macroFamily (X := X) d) ≤ K*modulus (C n) (H j) := by
    exact exists_modulus_localization (C n) (hC n) (macroFamily d) H
      (fun j => stripFamily_nonempty (e j))
      (fun _ _ h => stripFamily_member_nonempty h) hsub
  obtain ⟨j,N,hN,hNj⟩ := fixed_localization_subsequence
    (fun n => modulus (C n) (macroFamily (X := X) d))
    (fun j n => modulus (C n) (H j)) K hlocal
  refine ⟨e j,he j,hdiam j,K⁻¹,inv_pos.mpr hK,N,hN,?_⟩
  intro n
  calc
    K⁻¹ * modulus (C (N n)) (macroFamily d) ≤
        K⁻¹ * (K * modulus (C (N n)) (H j)) :=
      mul_le_mul_of_nonneg_left (hNj n) (inv_nonneg.mpr hK.le)
    _ = modulus (C (N n)) (stripFamily (e j)) := by rw [← mul_assoc,inv_mul_cancel₀ hK.ne',one_mul]

end CannonCharts

namespace CannonCharts

def squareMap (z : CannonGrid.Square) : Plane := (1+(z.1:ℝ),12*(z.2:ℝ)-6)

lemma continuous_squareMap : Continuous squareMap := by
  unfold squareMap
  fun_prop

lemma squareMap_injective : Function.Injective squareMap := by
  intro z w h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext
  · apply Subtype.ext
    dsimp [squareMap] at hx
    linarith
  · apply Subtype.ext
    dsimp [squareMap] at hy
    linarith

lemma squareMap_embedding : IsEmbedding squareMap :=
  (continuous_squareMap.isClosedEmbedding squareMap_injective).isEmbedding

lemma squareMap_in_box (z : CannonGrid.Square) :
    squareMap z ∈ Metric.closedBall 0 8 := by
  simp only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,
    max_le_iff,abs_le,squareMap]
  constructor <;> constructor <;> nlinarith [z.1.property.1,z.1.property.2,z.2.property.1,z.2.property.2]

theorem lift_strip_crossing (q : I → Plane) (hq : StripCrossing q) :
    ∃ u v : CannonRectangle.Middle, u.val.1 = 0 ∧ v.val.1 = 1 ∧
      ∃ p : Path u v, ∀ t, squareMap (p t).val = q t := by
  let m : I → CannonRectangle.Middle := fun t =>
    ⟨(⟨(q t).1-1,by constructor <;> linarith [(hq.2.2.2 t).1.1,(hq.2.2.2 t).1.2]⟩,
      ⟨((q t).2+6)/12,by
        have hy := abs_le.mp (hq.2.2.2 t).2
        constructor <;> linarith [hy.1,hy.2]⟩),by
      have hy := abs_le.mp (hq.2.2.2 t).2
      change ((q t).2+6)/12 ∈ Icc (1/3:ℝ) (2/3)
      constructor <;> linarith [hy.1,hy.2]⟩
  have hqc : Continuous q := hq.1
  have hm : Continuous m := by dsimp [m]; fun_prop
  let p : Path (m 0) (m 1) := ⟨⟨m,hm⟩,rfl,rfl⟩
  refine ⟨m 0,m 1,?_,?_,p,?_⟩
  · apply Subtype.ext
    change (q 0).1-1 = 0
    rw [hq.2.1]; norm_num
  · apply Subtype.ext
    change (q 1).1-1 = 1
    rw [hq.2.2.1]; norm_num
  · intro t
    apply Prod.ext <;> dsimp [squareMap,p,m] <;> ring

theorem stripFamily_eq_image {X : Type*} (e : Plane → X) :
    stripFamily e = {A | ∃ B ∈ CannonRectangle.leftRight, A = (e ∘ squareMap) '' B} := by
  ext A
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨u,v,hu,hv,p,hp⟩ := lift_strip_crossing q hq
    refine ⟨Subtype.val '' range p,⟨u,v,hu,hv,p,rfl⟩,?_⟩
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨(p t).val,⟨p t,⟨t,rfl⟩,rfl⟩,by dsimp; rw [hp]⟩
    · rintro ⟨z,⟨m,⟨t,rfl⟩,rfl⟩,rfl⟩
      exact ⟨t,by dsimp; rw [hp]⟩
  · rintro ⟨B,⟨u,v,hu,hv,p,rfl⟩,rfl⟩
    let q : I → Plane := fun t => squareMap (p t).val
    have hq : Continuous q := continuous_squareMap.comp (continuous_subtype_val.comp p.continuous)
    refine ⟨q,⟨hq,?_,?_,?_⟩,?_⟩
    · change 1+((p 0).val.1:ℝ) = 1
      rw [p.source,hu]
      norm_num
    · change 1+((p 1).val.1:ℝ) = 2
      rw [p.target,hv]
      norm_num
    · intro t
      have hy := (p t).property
      change ((p t).val.2:ℝ) ∈ Icc (1/3:ℝ) (2/3) at hy
      change 1+((p t).val.1:ℝ) ∈ Icc 1 2 ∧ |12*((p t).val.2:ℝ)-6| ≤ 2
      constructor
      · constructor <;> nlinarith [(p t).val.1.property.1,(p t).val.1.property.2]
      · rw [abs_le]
        constructor <;> linarith [hy.1,hy.2]
    · ext x
      constructor
      · rintro ⟨_,⟨_,⟨t,rfl⟩,rfl⟩,rfl⟩
        exact ⟨t,rfl⟩
      · rintro ⟨t,rfl⟩
        exact ⟨(p t).val,⟨p t,⟨t,rfl⟩,rfl⟩,rfl⟩

end CannonCharts

end
end
end
end
end
end
end
end
end

end OAI
