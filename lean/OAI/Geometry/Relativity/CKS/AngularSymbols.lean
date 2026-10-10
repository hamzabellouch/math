import OAI.Geometry.Relativity.CKS.TailDifferentiation
import OAI.Geometry.Relativity.CKS.TailSymbols

namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Set Filter Finset CKSSphericalHarmonics CKSInducedSphere CKSSphericalChart
open scoped Topology ContDiff

def angularPower (c : E → ℝ) (d : ℝ) (x : E) : ℝ := ‖x‖^(-d)*c (unitVector x)

def angularNext (c : E → ℝ) (d : ℝ) (j : Ix) (n : E) : ℝ :=
  (-d*n j)*c n + ∑ i : Ix, ((if i=j then 1 else 0)-n i*n j)*pd i c n

lemma angularNext_smooth {c : E → ℝ} (hc : ContDiffOn ℝ ∞ c U) (d : ℝ) (j : Ix) :
    ContDiffOn ℝ ∞ (angularNext c d j) U := by
  apply ContDiffOn.add
  · exact (contDiffOn_const.mul (coordinate_smooth j)).mul hc
  · apply ContDiffOn.sum
    intro i hi
    exact (contDiffOn_const.sub ((coordinate_smooth i).mul (coordinate_smooth j))).mul
      (partial_smooth hc i)

lemma angularPower_regular {c : E → ℝ} (hc : ContDiffOn ℝ ∞ c U) (d : ℝ) :
    TailRegular (angularPower c d) := by
  filter_upwards [eventually_norm_gt 0] with x hx
  have hn : x ≠ 0 := norm_pos_iff.mp hx
  have hh : ContDiffOn ℝ ∞ (fun z : ℝ × E => c z.2) heatDomain :=
    hc.comp contDiffOn_snd (fun z hz => hz)
  exact radialHeat_smooth (F := fun _ y => c y) hh 0 0 d hn

lemma angularPower_decay {c : E → ℝ} (hc : ContDiffOn ℝ ∞ c U) (d : ℝ) :
    Decay d (angularPower c d) := by
  let cr := smoothRestriction c hc
  refine ⟨‖cr‖,norm_nonneg _,?_⟩
  filter_upwards [eventually_norm_gt 0] with x hx
  have hn := unitVector_norm (norm_pos_iff.mp hx)
  let s : Sphere := ⟨unitVector x,by simpa [Metric.mem_sphere,dist_zero_right] using hn⟩
  have hh : |c (unitVector x)| ≤ ‖cr‖ := cr.norm_coe_le_norm s
  rw [angularPower,abs_mul,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (norm_nonneg _) _)).trans_eq (mul_comm _ _)

lemma pd_angularPower {c : E → ℝ} (hc : ContDiffOn ℝ ∞ c U) (d : ℝ) {x : E} (hx : x ≠ 0) (j : Ix) :
    pd j (angularPower c d) x = angularPower (angularNext c d j) (d+1) x := by
  have hh : ContDiffOn ℝ ∞ (fun z : ℝ × E => c z.2) heatDomain :=
    hc.comp contDiffOn_snd (fun z hz => hz)
  have he := pd_radialHeat (F := fun _ y => c y) hh 0 0 d hx j
  have heq : radialHeat (fun _ y => c y) 0 0 d = angularPower c d := rfl
  rw [heq] at he
  simpa only [radialHeat,radialNext,zero_mul,zero_add,add_zero,angularPower,angularNext] using he

theorem angularPower_symbol {c : E → ℝ} (hc : ContDiffOn ℝ ∞ c U) (d : ℝ) :
    Symbol d (angularPower c d) := by
  refine ⟨angularPower_regular hc d,?_⟩
  intro n
  induction n generalizing c d with
  | zero => exact angularPower_decay hc d
  | succ n ih =>
    refine ⟨angularPower_decay hc d,?_⟩
    intro j
    apply (ih (angularNext_smooth hc d j) (d+1)).congr
    filter_upwards [eventually_norm_gt 0] with x hx
    exact (pd_angularPower hc d (norm_pos_iff.mp hx) j).symm

lemma norm_power_symbol (d : ℝ) : Symbol d (fun x : E => ‖x‖^(-d)) := by
  have hh := angularPower_symbol (c := fun _ => 1) contDiffOn_const d
  convert hh using 1
  funext x
  simp [angularPower]

lemma normal_symbol (i : Ix) : Symbol 0 (fun x : E => normal x i) := by
  have hh := angularPower_symbol (coordinate_smooth i) 0
  convert hh using 1
  funext x
  simp [angularPower,unitVector_component]

lemma SymbolN.word {F : E → ℝ} {d : ℝ} (hF : Symbol d F) (w : List Ix) :
    Decay (d+w.length) (cartWord w F) := by
  induction w generalizing F d with
  | nil =>
    simp only [cartWord,List.length_nil,Nat.cast_zero,add_zero]
    exact hF.2 0
  | cons j w ih =>
    have hh := ih (hF.pd j)
    convert hh using 1 <;> simp only [cartWord,List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

lemma symbol_of_words {F : E → ℝ} {d : ℝ} (hr : TailRegular F)
    (hw : ∀ w : List Ix, Decay (d+w.length) (cartWord w F)) : Symbol d F := by
  refine ⟨hr,?_⟩
  intro n
  induction n generalizing F d with
  | zero =>
    change Decay d F
    simpa only [cartWord,List.length_nil,Nat.cast_zero,add_zero] using hw []
  | succ n ih =>
    refine ⟨?_,?_⟩
    · simpa only [cartWord,List.length_nil,Nat.cast_zero,add_zero] using hw []
    · intro j
      apply ih (hr.pd j)
      intro w
      convert hw (j::w) using 1 <;> simp only [cartWord,List.length_cons,Nat.cast_add,Nat.cast_one]
      ring

end
end CKSADM

end

end OAI
