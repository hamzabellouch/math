import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorNormalized
import OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorDyadic
import OAI.NumberTheory.DirichletL.PrimeRows.CubeBinPartition

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

def sourceDyadExponent (Z : ℝ) (k : ℕ) : ℝ := Real.logb Z ((2:ℝ)^k)
def sourceDyadConductor (Z margin : ℝ) (k : ℕ) : ℝ := sourceDyadExponent Z k+2*margin

lemma sourceDyad_scale {Z : ℝ} (hZ : 1<Z) (k : ℕ) :
    Z^(sourceDyadExponent Z k)=(2:ℝ)^k :=
  Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (by positivity)

lemma canonical_dyad_cost (loss : ℝ) (hl : 0<loss) :
    ∃C : ℝ,0<C ∧ ∀(Z v : ℝ),1≤Z → v≤1 →
      ((smallDyadicIndices (Z^v)).card:ℝ)≤C*Z^loss := by
  obtain ⟨C,hC,hbound⟩ := bounded_dyadic_power_sum loss hl
  refine ⟨C,hC,?_⟩
  intro Z v hZ hv
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  calc
    _ = ∑k∈smallDyadicIndices (Z^v),(1:ℝ) := by simp
    _ ≤ ∑k∈smallDyadicIndices (Z^v),((2:ℝ)^k)^loss := by
      apply Finset.sum_le_sum
      intro k hk
      exact Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) hl.le
    _ ≤ C*(Z^v)^loss := hbound _ (by positivity) _ (fun k hk=>mem_smallDyadicIndices.mp hk)
    _ ≤ C*Z^loss := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      rw [←Real.rpow_mul hZp.le]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

lemma sourceDyad_geometry_eventually (dmin dmax margin vmax : ℝ)
    (_hdmin : 0<dmin) (hdmin1 : dmin<1/100) (hmargin : 0<margin)
    (hdmax : vmax+2*margin≤dmax) :
    ∀ᶠZ : ℝ in atTop,∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^vmax) →
      ∀k : ℕ,(rows∩dyadicRows 1 k).Nonempty →
        0≤sourceDyadExponent Z k ∧ sourceDyadExponent Z k≤vmax ∧
        dmin≤sourceDyadConductor Z margin k ∧ sourceDyadConductor Z margin k≤dmax ∧
        (∀u∈rows∩dyadicRows 1 k,
          Z^(sourceDyadExponent Z k)≤rowNorm u ∧ rowNorm u≤2*Z^(sourceDyadExponent Z k)) ∧
        (∀u∈rows∩dyadicRows 1 k,rowNorm u≤Z^(sourceDyadConductor Z margin k-margin)) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0<(1/100:ℝ)-dmin by linarith)).eventually (eventually_ge_atTop (2:ℝ)),
    (tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop (2:ℝ))] with Z hZ hsmall hmarginZ
  intro rows hrows k hne
  have hZp : 0<Z := zero_lt_one.trans hZ
  obtain ⟨u,hu⟩ := hne
  have hur := (Finset.mem_inter.mp hu).1
  have hud := mem_dyadicRows.mp (Finset.mem_inter.mp hu).2
  have hlow : (2:ℝ)^k≤rowNorm u := by simpa only [one_mul] using hud.2.1
  have hhigh : rowNorm u<2*(2:ℝ)^k := by simpa only [one_mul] using hud.2.2
  have hv0 : 0≤sourceDyadExponent Z k := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [sourceDyad_scale hZ,Real.rpow_zero]
    exact one_le_pow₀ (by norm_num)
  have hvmax : sourceDyadExponent Z k≤vmax := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [sourceDyad_scale hZ]
    exact hlow.trans (hrows u hur).2.2
  have hvmin : dmin≤sourceDyadExponent Z k := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [sourceDyad_scale hZ]
    have hh : 2*Z^dmin≤Z^(1/100:ℝ) := by
      calc
        _ ≤ Z^((1/100:ℝ)-dmin)*Z^dmin := mul_le_mul_of_nonneg_right hsmall (by positivity)
        _ = _ := by rw [←Real.rpow_add hZp];congr 1;ring
    linarith [(hrows u hur).2.1]
  have hnorm : ∀u∈rows∩dyadicRows 1 k,
      Z^(sourceDyadExponent Z k)≤rowNorm u ∧ rowNorm u≤2*Z^(sourceDyadExponent Z k) := by
    intro u hu
    rw [sourceDyad_scale hZ]
    have hh := (mem_dyadicRows.mp (Finset.mem_inter.mp hu).2).2
    simpa only [one_mul] using And.intro hh.1 hh.2.le
  refine ⟨hv0,hvmax,?_,?_,hnorm,?_⟩
  · unfold sourceDyadConductor;linarith
  · unfold sourceDyadConductor;linarith
  · exact dyad_conductor_margin Z (sourceDyadExponent Z k) margin hZp hmarginZ _ (fun u hu=>(hnorm u hu).2)

end SevenEighths.ProbeHighRowFamily

end

end OAI
