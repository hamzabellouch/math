import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open Set

open scoped BigOperators

namespace Kadison.DeMarrCenter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_center {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (D : ℝ) (hD : 0<D) (hdiam : ∀ x∈K,∀ y∈K,dist x y≤D) :
    ∃ c∈convexHull ℝ K,∃ r : ℝ,0≤r ∧ r<D ∧ ∀ x∈K,dist c x≤r := by
  classical
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun x : K => Metric.ball (x:E) (D/2))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,by simpa only [Metric.mem_ball,dist_self] using half_pos hD⟩)
  have htn : t.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    obtain ⟨i,hi,_⟩ := mem_iUnion₂.mp (ht hx)
    exact ⟨i,hi⟩
  have hcard : 0<(t.card : ℝ) := by exact_mod_cast htn.card_pos
  let c : E := (t.card : ℝ)⁻¹ • ∑ i∈t,(i:E)
  let r : ℝ := (t.card : ℝ)⁻¹*(D/2+((t.erase htn.choose).card : ℝ)*D)
  have herase (i : K) (hi : i∈t) : ((t.erase i).card : ℝ)=(t.card : ℝ)-1 := by
    have hc := Finset.card_erase_add_one hi
    have hc' : ((t.erase i).card : ℝ)+1=(t.card : ℝ) := by exact_mod_cast hc
    linarith
  have hcent : c∈convexHull ℝ K := by
    have hh := t.centerMass_mem_convexHull (R:=ℝ) (s:=K) (w:=fun _ => (1:ℝ))
      (fun _ _ => zero_le_one) (by simpa only [Finset.sum_const,nsmul_eq_mul,smul_eq_mul,mul_one] using hcard)
      (fun i _ => i.property)
    simpa only [Finset.centerMass,Finset.sum_const,nsmul_eq_mul,smul_eq_mul,mul_one,one_smul] using hh
  have hr : 0≤r := mul_nonneg (inv_nonneg.mpr hcard.le)
    (add_nonneg (half_pos hD).le (mul_nonneg (Nat.cast_nonneg _) hD.le))
  have hrD : r<D := by
    dsimp [r]
    rw [herase _ htn.choose_spec]
    apply (inv_mul_lt_iff₀ hcard).mpr
    nlinarith
  refine ⟨c,hcent,r,hr,hrD,?_⟩
  intro x hx
  obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (ht hx)
  have hid : dist (i:E) x≤D/2 := by
    rw [dist_comm]
    exact hxi.le
  have hs : ∑ j∈t,dist (j:E) x≤D/2+((t.erase i).card : ℝ)*D := by
    rw [←Finset.sum_erase_add _ _ hi]
    have hb : ∑ j∈t.erase i,dist (j:E) x≤((t.erase i).card : ℝ)*D := by
      simpa only [Finset.sum_const,nsmul_eq_mul] using
        (Finset.sum_le_sum (s:=t.erase i) (fun j _ => hdiam j j.property x hx))
    linarith
  have hcx : c-x=(t.card : ℝ)⁻¹ • ∑ j∈t,((j:E)-x) := by
    rw [Finset.sum_sub_distrib,smul_sub,Finset.sum_const,← Nat.cast_smul_eq_nsmul ℝ]
    dsimp [c]
    rw [smul_smul,inv_mul_cancel₀ hcard.ne',one_smul]
  rw [dist_eq_norm,hcx,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hcard)]
  calc
    _ ≤ (t.card : ℝ)⁻¹*∑ j∈t,‖(j:E)-x‖ := mul_le_mul_of_nonneg_left
      (norm_sum_le _ _) (inv_nonneg.mpr hcard.le)
    _ ≤ (t.card : ℝ)⁻¹*(D/2+((t.erase i).card : ℝ)*D) := by
      simp only [←dist_eq_norm]
      exact mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hcard.le)
    _ = r := by dsimp [r]; rw [herase i hi,herase _ htn.choose_spec]

end Kadison.DeMarrCenter

end

end
end

end OAI
