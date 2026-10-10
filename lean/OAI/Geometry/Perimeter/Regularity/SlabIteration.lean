import OAI.Geometry.Perimeter.Regularity.FlatnessImprovement

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

@[simp] theorem blownUpSet_zero_one (E : Set (Euc n)) : blownUpSet E 0 1=E := by
  ext x; simp [blownUpSet]

theorem blownUpSet_zero_comp (E : Set (Euc n)) (s t : ℝ) :
    blownUpSet (blownUpSet E 0 s) 0 t=blownUpSet E 0 (s*t) := by
  ext x; simp [blownUpSet,smul_smul]

def SlabContractionProperty (n : ℕ) (q M δ : ℝ) : Prop :=
  ∀ (E : Set (Euc n)), IsLocallyPerimeterMinimizing E →
    (0:Euc n)∈perimeterSupport E → ∀ (v : Euc n), ‖v‖=1 →
      ∀ a : ℝ, 0 < a → a < δ → FullSlab E v 8 a →
        ∃ w : Euc n, ‖w‖=1 ∧ ‖w-v‖≤M*a ∧ FullSlab (blownUpSet E 0 q) w 8 (a/2)

theorem slab_normal_sequence {q M δ : ℝ} (hq : 0 < q)
    (hstep : SlabContractionProperty n q M δ) {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) (hzero : (0:Euc n)∈perimeterSupport E)
    {v₀ : Euc n} (hv₀ : ‖v₀‖=1) {a : ℝ} (ha : 0 < a) (haδ : a < δ)
    (hs : FullSlab E v₀ 8 a) :
    ∃ v : ℕ → Euc n, v 0=v₀ ∧ (∀ j, ‖v j‖=1) ∧
      (∀ j, FullSlab (blownUpSet E 0 (q^j)) (v j) 8 (a*(1/2)^j)) ∧
      (∀ j, ‖v (j+1)-v j‖≤M*a*(1/2)^j) := by
  let S (j : ℕ) := {v : Euc n // ‖v‖=1 ∧ FullSlab (blownUpSet E 0 (q^j)) v 8 (a*(1/2)^j)}
  have hnext (j : ℕ) (s : S j) : ∃ t : S (j+1), ‖t.val-s.val‖≤M*a*(1/2)^j := by
    have hminj := locally_minimizing_blownUpSet hmin 0 (pow_pos hq j)
    have hzj : (0:Euc n)∈perimeterSupport (blownUpSet E 0 (q^j)) := by
      apply (perimeterSupport_blownUpSet hmin.1 0 (pow_pos hq j) 0).mpr
      simpa only [smul_zero,zero_add] using hzero
    have haj : 0 < a*(1/2:ℝ)^j := mul_pos ha (pow_pos (by norm_num) _)
    have hadj : a*(1/2:ℝ)^j < δ :=
      (mul_le_of_le_one_right ha.le (pow_le_one₀ (by norm_num) (by norm_num))).trans_lt haδ
    obtain ⟨w,hw,hwd,hws⟩ := hstep _ hminj hzj s.val s.property.1 _ haj hadj s.property.2
    rw [blownUpSet_zero_comp,← pow_succ] at hws
    have hpow : a*(1/2:ℝ)^j/2=a*(1/2:ℝ)^(j+1) := by rw [pow_succ]; ring
    rw [hpow] at hws
    exact ⟨⟨w,hw,hws⟩,by simpa only [mul_assoc] using hwd⟩
  choose next hnext using hnext
  let s₀ : S 0 := ⟨v₀,hv₀,by simpa only [pow_zero,mul_one,blownUpSet_zero_one] using hs⟩
  let s : (j : ℕ) → S j := fun j ↦ Nat.rec s₀ (fun j t ↦ next j t) j
  refine ⟨fun j ↦ (s j).val,rfl,fun j ↦ (s j).property.1,fun j ↦ (s j).property.2,?_⟩
  intro j
  exact hnext j (s j)

theorem slab_normal_limit {q M δ : ℝ} (hq : 0 < q)
    (hstep : SlabContractionProperty n q M δ) {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) (hzero : (0:Euc n)∈perimeterSupport E)
    {v₀ : Euc n} (hv₀ : ‖v₀‖=1) {a : ℝ} (ha : 0 < a) (haδ : a < δ)
    (hs : FullSlab E v₀ 8 a) :
    ∃ v : ℕ → Euc n, ∃ w : Euc n, v 0=v₀ ∧ (∀ j, ‖v j‖=1) ∧ ‖w‖=1 ∧
      Tendsto v atTop (𝓝 w) ∧
      (∀ j, FullSlab (blownUpSet E 0 (q^j)) (v j) 8 (a*(1/2)^j)) ∧
      (∀ j, ‖v j-w‖≤2*M*a*(1/2)^j) := by
  obtain ⟨v,hv0,hunit,hslab,hinc⟩ := slab_normal_sequence hq hstep hmin hzero hv₀ ha haδ hs
  have hdist (j : ℕ) : dist (v j) (v (j+1))≤(M*a)*(1/2:ℝ)^j := by
    rw [dist_eq_norm,norm_sub_rev]
    exact hinc j
  obtain ⟨w,hw⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1/2) (M*a) (by norm_num) hdist)
  have hwn : ‖w‖=1 := tendsto_nhds_unique hw.norm (by simpa only [hunit] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1:ℝ)) atTop (𝓝 1)))
  refine ⟨v,w,hv0,hunit,hwn,hw,hslab,fun j ↦ ?_⟩
  have hh := dist_le_of_le_geometric_of_tendsto (1/2) (M*a) (by norm_num) hdist hw j
  rw [dist_eq_norm] at hh
  convert hh using 1
  ring

end RPISingularHarnack

end

end OAI
