import Mathlib
import OAI.Geometry.Cannon.CirclePacking.AngleGradient

namespace OAI

/-! Strict cut inequalities yield coherent angles and circle radii. -/

section
section
section
section
noncomputable section
namespace CannonPackingGeometry
open Finset Set Function

variable {V F : Type*} [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]

theorem strict_cuts_give_angles (vertex : F × Fin 3 → V)
    (hinj : ∀ f, Injective (fun k => vertex (f,k)))
    (d : V → ℕ) (hd : ∀ v, 0<d v)
    (hcut : ∀ S : Finset V, S.Nonempty → S≠Finset.univ →
      (∑ v∈S,d v) < 3 * (neighborFaces (fun v f => ∃ k, vertex (f,k)=v) S).card)
    (htotal : ∑ v,d v = 3 * Fintype.card F) :
    ∃ s : F × Fin 3 → ℝ, (∀ i, s i ∈ Ioo (0:ℝ) Real.pi) ∧
      (∀ f, ∑ k : Fin 3, s (f,k)=Real.pi) ∧
      ∀ v, (∑ i : F × Fin 3, if vertex i=v then s i else 0)=Real.pi/3*(d v:ℝ) := by
  classical
  let R : V → F → Prop := fun v f => ∃ k, vertex (f,k)=v
  obtain ⟨w,hwp,hwz,hwv,hwf⟩ := positive_transport R d (fun _ => 3) hd
    (fun _ => by norm_num) (fun f => ⟨vertex (f,0),0,rfl⟩)
    (by intro S hs ht; simpa [R,sum_const,smul_eq_mul,mul_comm] using hcut S hs ht)
    (by simpa [sum_const,smul_eq_mul,mul_comm] using htotal)
  have hface (f : F) : ∑ k : Fin 3, w (vertex (f,k)) f=3 := by
    calc
      _ = ∑ v, w v f := Fintype.sum_of_injective (fun k => vertex (f,k)) (hinj f)
        _ _ (fun v hv => hwz v f hv) (fun _ => rfl)
      _ = 3 := by simpa using hwf f
  have hpos (f : F) (k : Fin 3) : 0<w (vertex (f,k)) f := hwp _ _ ⟨k,rfl⟩
  have hlt (f : F) (k : Fin 3) : w (vertex (f,k)) f<3 := by
    have hh := hface f
    simp only [Fin.sum_univ_three] at hh
    have h0 := hpos f 0
    have h1 := hpos f 1
    have h2 := hpos f 2
    fin_cases k
    · change w (vertex (f,0)) f<3
      linarith
    · change w (vertex (f,1)) f<3
      linarith
    · change w (vertex (f,2)) f<3
      linarith
  have hvertex (v : V) (f : F) :
      ∑ k : Fin 3, (if vertex (f,k)=v then w (vertex (f,k)) f else 0)=w v f := by
    calc
      _ = ∑ u : V, if u=v then w u f else 0 := by
        apply Fintype.sum_of_injective (fun k => vertex (f,k)) (hinj f)
        · intro u hu
          by_cases huv : u=v
          · subst u
            simp [hwz v f hu]
          · simp [huv]
        · intro k
          rfl
      _ = w v f := by simp
  let s : F × Fin 3 → ℝ := fun i => Real.pi/3*w (vertex i) i.1
  refine ⟨s,?_,?_,?_⟩
  · rintro ⟨f,k⟩
    have hp : 0<Real.pi/3 := div_pos Real.pi_pos (by norm_num)
    constructor
    · exact mul_pos hp (hpos f k)
    · have hh := mul_lt_mul_of_pos_left (hlt f k) hp
      dsimp [s]
      nlinarith
  · intro f
    change (∑ k : Fin 3, Real.pi/3*w (vertex (f,k)) f)=Real.pi
    rw [←mul_sum,hface]
    ring
  · intro v
    have hi (i : F × Fin 3) :
        (if vertex i=v then s i else 0) = Real.pi/3*(if vertex i=v then w (vertex i) i.1 else 0) := by
      by_cases h : vertex i=v <;> simp [s,h]
    simp_rw [hi]
    rw [←mul_sum,Fintype.sum_prod_type]
    simp_rw [hvertex]
    rw [hwv]

end CannonPackingGeometry

end
end
namespace CannonPackingGeometry
open Set Function

variable {V F : Type*} [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]

theorem strict_cuts_give_radii (vertex : F × Fin 3 → V)
    (hinj : ∀ f, Injective (fun k => vertex (f,k)))
    (d : V → ℕ) (hd : ∀ v, 0<d v)
    (hcut : ∀ S : Finset V, S.Nonempty → S≠Finset.univ →
      (∑ v∈S,d v) < 3 * (neighborFaces (fun v f => ∃ k, vertex (f,k)=v) S).card)
    (htotal : ∑ v,d v = 3 * Fintype.card F) :
    ∃ (θ : F × Fin 3 → ℝ) (r : V → ℝ) (q : F → ℝ),
      (∀ i, θ i ∈ Ioo (0:ℝ) Real.pi) ∧
      (∀ f, ∑ k : Fin 3, θ (f,k)=Real.pi) ∧
      (∀ v, (∑ i : F × Fin 3, if vertex i=v then θ i else 0)=Real.pi/3*(d v:ℝ)) ∧
      (∀ v, 0<r v) ∧ (∀ f, 0<q f) ∧
      ∀ i, Real.tan (θ i/2)=q i.1/r (vertex i) := by
  obtain ⟨s,hs,hsf,hsv⟩ := strict_cuts_give_angles vertex hinj d hd hcut htotal
  exact coherent_angles_give_radii vertex (fun v => Real.pi/3*(d v:ℝ)) s hs hsf hsv
end CannonPackingGeometry

end
end
end

end OAI
