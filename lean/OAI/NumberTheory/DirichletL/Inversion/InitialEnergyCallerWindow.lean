import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerPool
import OAI.NumberTheory.DirichletL.Inversion.InitialRawDictionary

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseInitialPoissonBridge SevenEighths.InverseInitialKernelBridge SevenEighths.InverseInitialEnergyCallerPool
namespace SevenEighths.InverseInitialEnergyCallerWindow
local notation "Eis" => ActualEisensteinCubic.O

def originalSource (Z r b : ℝ) : Finset (Ideal Eis) :=
  (idealsUpTo ⌈Z^r*b⌉₊).filter Supported

theorem originalSource_supported (Z r b : ℝ) :
    ∀n∈originalSource Z r b,Squarefree n→Supported n := by
  intro n hn _
  exact (Finset.mem_filter.mp hn).2

theorem residual_window_eq (W : ℝ→ℂ) {P j c : Ideal Eis}
    (hP : Squarefree P) (hj : j∣P) (hc : residual P j∣c)
    (Z r z G : ℝ) (hZ : 0<Z) :
    residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G)) =
      W (((reconstruct P j c).absNorm:ℝ)/Z^r) := by
  unfold residualOverlapWindow
  rw [←scaled_cutoff_argument hP hj hc hZ r z G]

theorem reconstructed_mem_originalSource
    (W : ℝ→ℂ) (Z r z G b : ℝ) (hZ : 0<Z) (hW : ∀x,W x≠0→x≤b)
    {P j c : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (hc : Admissible c) (hPc : residual P j∣c)
    (hlive : residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G))≠0) :
    reconstruct P j c∈originalSource Z r b := by
  have hs : Supported (reconstruct P j c) :=
    (supported_mul_iff _ _).mpr
      ⟨admissible_supported (admissible_of_dvd hP hj),
        admissible_supported (admissible_of_dvd hc (idealQuotient_dvd hPc))⟩
  apply Finset.mem_filter.mpr
  refine ⟨InverseInitialRawDictionary.finite_source_cover W (Z^r) b
    (Real.rpow_pos_of_pos hZ r) hW _ hs.1 ?_,hs⟩
  rwa [residual_window_eq W hP.2.1 hj hPc Z r z G hZ] at hlive

theorem original_selector_window
    (W : ℝ→ℂ) (Z r z G b : ℝ) (hZ : 0<Z) (hW : ∀x,W x≠0→x≤b)
    {P j : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (hne : (columns (originalSource Z r b) P j).Nonempty)
    (a : Ideal Eis→ℂ) (A : Finset (primePool (columns (originalSource Z r b) P j))) :
    reconstructedSelector (originalSource Z r b) P j a A *
      rowCoprimeMask (fun i : primePool (columns (originalSource Z r b) P j)=>i.val)
        A (primaryGenerator j) *
      residualOverlapWindow P j W Z z G (((∏ i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) =
    a (reconstruct P j (∏ i∈A,i.val)) *
      InverseMoment.primeMark (forcedSlots (originalSource Z r b) P j) (fun i=>{i})
        (fun _ _=>(1:ℂ)) A *
      rowCoprimeMask (fun i : primePool (columns (originalSource Z r b) P j)=>i.val)
        A (primaryGenerator j) *
      residualOverlapWindow P j W Z z G (((∏ i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) := by
  have hF : ∀I∈columns (originalSource Z r b) P j,Admissible I :=
    fun I hI=>columns_admissible _ hP hj (originalSource_supported Z r b) hI
  have hA := InitialMeanSquare.poolProduct_admissible _ hF A
  apply original_selector_forced_slots _ hP hj hne a
    (fun c=>residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G))) A hA.2.1
  intro hPc hlive _
  exact reconstructed_mem_originalSource W Z r z G b hZ hW hP hj hA hPc hlive

end SevenEighths.InverseInitialEnergyCallerWindow

end

end OAI
