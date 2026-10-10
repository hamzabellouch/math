import OAI.Analysis.PlanarPacking.Certificate.TableDensity0Panel0
import OAI.Analysis.PlanarPacking.Certificate.TableDensity0Panel1
import OAI.Analysis.PlanarPacking.Certificate.TableDensity0Panel2
import OAI.Analysis.PlanarPacking.Certificate.TableDensity0Panel3
import OAI.Analysis.PlanarPacking.Certificate.TableDensity0Panel4
import OAI.Analysis.PlanarPacking.Certificate.TableDensity0Panel5
import OAI.Analysis.PlanarPacking.Certificate.TableDensity1Panel0
import OAI.Analysis.PlanarPacking.Certificate.TableDensity1Panel1
import OAI.Analysis.PlanarPacking.Certificate.TableDensity1Panel2
import OAI.Analysis.PlanarPacking.Certificate.TableDensity1Panel3
import OAI.Analysis.PlanarPacking.Certificate.TableDensity1Panel4
import OAI.Analysis.PlanarPacking.Certificate.TableDensity1Panel5

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
noncomputable def density0 : Fin 6 → Fin 16 → Fin 16 → CBox := ![density0_r0,density0_r1,density0_r2,density0_r3,density0_r4,density0_r5]
lemma density0_eq (j : Fin 6) (i k : Fin 16) : density0Expr j i k = density0 j i k := by
  fin_cases j
  · exact density0_r0_eq i k
  · exact density0_r1_eq i k
  · exact density0_r2_eq i k
  · exact density0_r3_eq i k
  · exact density0_r4_eq i k
  · exact density0_r5_eq i k
lemma density0_contains (j : Fin 6) (i k : Fin 16) :
    (density0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*tableDensity false j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← density0_eq,tableDensity_weighted]
  exact finSum_contains (fun n => CBox.contains_add (tableTerm_contains false false n j i k) (tableTerm_contains false true n j i k))
noncomputable def density1 : Fin 6 → Fin 16 → Fin 16 → CBox := ![density1_r0,density1_r1,density1_r2,density1_r3,density1_r4,density1_r5]
lemma density1_eq (j : Fin 6) (i k : Fin 16) : density1Expr j i k = density1 j i k := by
  fin_cases j
  · exact density1_r0_eq i k
  · exact density1_r1_eq i k
  · exact density1_r2_eq i k
  · exact density1_r3_eq i k
  · exact density1_r4_eq i k
  · exact density1_r5_eq i k
lemma density1_contains (j : Fin 6) (i k : Fin 16) :
    (density1 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*tableDensity true j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← density1_eq,tableDensity_weighted]
  exact finSum_contains (fun n => CBox.contains_add (tableTerm_contains true false n j i k) (tableTerm_contains true true n j i k))
end SharpPlanar.CachedData

end OAI
