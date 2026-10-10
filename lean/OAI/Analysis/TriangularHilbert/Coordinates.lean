import OAI.Analysis.TriangularHilbert.CyclicNorm

namespace OAI

section
namespace TriangularHilbert
open MeasureTheory MeasureTheory.Measure Heat
open scoped ENNReal
noncomputable section

def chartB (z : Plane) : Plane := (z.1+z.2,-z.1)
def chartC (z : Plane) : Plane := (-z.2,z.1+z.2)
def cyclicB (F : Plane → ℂ) : Plane → ℂ := F ∘ chartB
def cyclicC (G : Plane → ℂ) : Plane → ℂ := G ∘ chartC

lemma measurePreserving_chartB : MeasurePreserving chartB volume volume := by
  exact measurePreserving_add_prod_neg_right (volume : Measure ℝ) volume

lemma measurePreserving_chartC : MeasurePreserving chartC volume volume := by
  have hs : MeasurePreserving (Prod.swap : Plane → Plane) volume volume := measurePreserving_swap
  have h := (hs.comp measurePreserving_chartB).comp hs
  convert h using 1
  funext z
  simp only [Function.comp_apply,chartC,chartB,Prod.swap,add_comm]

lemma measurePreserving_reflect : MeasurePreserving (fun z : Plane => -z) volume volume :=
  volume.measurePreserving_neg

lemma memLp_cyclicB {F : Plane → ℂ} (hF : MemLp F 3 volume) : MemLp (cyclicB F) 3 volume :=
  hF.comp_measurePreserving measurePreserving_chartB
lemma memLp_cyclicC {G : Plane → ℂ} (hG : MemLp G 3 volume) : MemLp (cyclicC G) 3 volume :=
  hG.comp_measurePreserving measurePreserving_chartC

lemma eLpNorm_cyclicB {F : Plane → ℂ} (hF : MemLp F 3 volume) :
    eLpNorm (cyclicB F) 3 volume = eLpNorm F 3 volume :=
  eLpNorm_comp_measurePreserving hF.aestronglyMeasurable measurePreserving_chartB
lemma eLpNorm_cyclicC {G : Plane → ℂ} (hG : MemLp G 3 volume) :
    eLpNorm (cyclicC G) 3 volume = eLpNorm G 3 volume :=
  eLpNorm_comp_measurePreserving hG.aestronglyMeasurable measurePreserving_chartC

lemma measurableSet_annulus (r R : ℝ) : MeasurableSet (annulus r R) :=
  (isOpen_lt continuous_const continuous_abs).measurableSet.inter
    (isOpen_lt continuous_abs continuous_const).measurableSet

lemma hardKernel_eq_indicator_ae {r R : ℝ} (hR : r ≤ R) :
    (fun t => hardKernel r R t) =ᵐ[volume]
      (annulus r R).indicator (fun t : ℝ => 1/t) := by
  have hne (x : ℝ) : ∀ᵐ t : ℝ, t ≠ x := by simp [ae_iff]
  filter_upwards [hne R,hne (-R)] with t ht1 ht2
  have ht : |t| ≠ R := by
    intro he
    rcases eq_or_eq_neg_of_abs_eq he with he|he
    · exact ht1 he
    · exact ht2 he
  classical
  by_cases h1 : r < |t|
  · by_cases h2 : |t| < R
    · simp only [hardKernel,h1,ite_true,not_lt.mpr h2.le,ite_false,sub_zero,
        Set.indicator_of_mem (show t ∈ annulus r R from ⟨h1,h2⟩)]
    · have h3 : R < |t| := lt_of_le_of_ne (le_of_not_gt h2) (Ne.symm ht)
      simp only [hardKernel,h1,h3,ite_true,sub_self,zero_div,
        Set.indicator_of_notMem (show t ∉ annulus r R from fun h => h2 h.2)]
  · have h2 : ¬ R < |t| := not_lt.mpr ((le_of_not_gt h1).trans hR)
    simp only [hardKernel,h1,h2,ite_false,sub_self,zero_div,
      Set.indicator_of_notMem (show t ∉ annulus r R from fun h => h1 h.1)]

lemma cyclicHard_coordinate_integrand (F G : Plane → ℂ) (z : Plane) (r R t : ℝ) :
    cyclicB F ((-z).2,t+z.1+z.2) * cyclicC G (t+z.1+z.2,(-z).1) *
      (hardKernel r R ((-z).1+(-z).2+(t+z.1+z.2)):ℂ) =
    F (z.1+t,z.2)*G (z.1,z.2+t)*(hardKernel r R t:ℂ) := by
  change F (-z.2+(t+z.1+z.2),-(-z.2))*G (-(-z.1),(t+z.1+z.2)+(-z.1))*
    (hardKernel r R (-z.1 + -z.2+(t+z.1+z.2)):ℂ) = _
  rw [show -z.2+(t+z.1+z.2) = z.1+t by ring,
    show (t+z.1+z.2)+(-z.1) = z.2+t by ring,
    show -z.1 + -z.2+(t+z.1+z.2) = t by ring]
  simp only [neg_neg]
end
end TriangularHilbert
end

end OAI
