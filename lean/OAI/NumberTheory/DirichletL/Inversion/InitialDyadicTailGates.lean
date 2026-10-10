import OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyTail
import OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailAnnulus
import OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailRapid

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialDyadicTailBound
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialDyadicAssembly InverseInitialProfile
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem pointSource_erase_mem (pool : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (x : Point ι) (hx : x∈pointSource pool S) : erasePoint x∈S := by
  obtain ⟨y,hy,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hx
  simpa only [erase_sourcePoint] using hy

theorem pointSource_supports (pool : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (hC : ∀x∈S,x.common⊆pool) (hV : ∀x∈S,x.overlap⊆pool)
    (hdiv : ∀x∈S,x.divisor⊆x.common)
    (x : Point ι) (hx : x∈pointSource pool S) :
    ∀i,InverseInitialHighFrequencyTail.sourceKey x i⊆pool := by
  obtain ⟨y,hy,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hx
  intro i
  fin_cases i
  · exact hC y hy
  · exact (hdiv y hy).trans (hC y hy)
  · exact hV y hy
  · exact (Finset.mem_powerset.mp (Finset.mem_product.mp hNM).1).trans Finset.sdiff_subset
  · exact (Finset.mem_powerset.mp (Finset.mem_product.mp hNM).2).trans Finset.sdiff_subset

def idealIndex : Fin 5→Fin 6 := ![0,1,2,4,5]

omit [DecidableEq ι] in
theorem sourceKey_norm_coordinate (p : ι→O) (x : Point ι) (i : Fin 5) :
    primeProductNorm p (InverseInitialHighFrequencyTail.sourceKey x i)=coordinates p x (idealIndex i) := by
  have hn (A : Finset ι) : ((sourceIdeal p A).absNorm:ℝ)=primeProductNorm p A := by
    rw [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span]
    rfl
  fin_cases i <;> simp [InverseInitialHighFrequencyTail.sourceKey,coordinates,physicalCoordinates,idealIndex,hn]

omit [DecidableEq ι] in
theorem sourceNorms_erase (p : ι→O) (x : Point ι) (i : Fin 4) :
    sourceNorms p (erasePoint x) i=coordinates p x (InverseSecondChildWindows.outerIndex i) := by
  have he : InverseInitialEnergyCallerModes.sourcePoint (erasePoint x) x.left x.right=x := by
    cases x
    rfl
  simpa only [he] using sourceNorms_fresh p (erasePoint x) x.left x.right i

omit [DecidableEq ι] in
theorem live_mass_radial_gate
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (a b : Fin 4→ℝ) (Z D m η τ bW : ℝ) (hZ : 1<Z) (hη : 0≤η)
    (hbW : 0<bW) (hfixed : 64*bW^2≤Z^η)
    (x : Point ι) (hx : Valid x)
    (hleft : coordinates p x 0*coordinates p x 2*coordinates p x 4≤bW*Z^D)
    (hright : coordinates p x 0*coordinates p x 2*coordinates p x 5≤bW*Z^D)
    (hmass : windowMass (tailWindows a b Z D m (4*η+τ)) (sourceNorms p (erasePoint x))≠0) :
    Z^τ≤(Z^m/(primeProductNorm p x.divisor*(primeProductNorm p x.overlap)^2*
      primeProductNorm p x.left*primeProductNorm p x.right))*‖eisEmbedding x.frequency‖^2 := by
  obtain ⟨k,hk,hhigh,hbounds⟩ := tail_mass_live_bounds p a b Z D m (4*η+τ) hZ (erasePoint x) hmass
  have hc := coordinates_pos p hp x hx
  have h₀ := (hbounds 0).1.le
  have h₁ := (hbounds 1).2.le
  have h₃ := (hbounds 3).1.le
  rw [sourceNorms_erase] at h₀ h₁ h₃
  have hh := InverseInitialHighFrequencyTail.actual_annulus_high_gate Z D m
    (exponent Z (k 0).val) (exponent Z (k 1).val) (exponent Z (k 3).val) η τ bW
    (coordinates p x 0) (coordinates p x 1) (coordinates p x 2)
    (coordinates p x 4) (coordinates p x 5) (coordinates p x 3)
    hZ.le hη hbW (hc 1) (hc 2) (hc 4) (hc 5) h₀ h₁ h₃ hleft hright hfixed hhigh.le
  have hn (A : Finset ι) : ((sourceIdeal p A).absNorm:ℝ)=primeProductNorm p A := by
    rw [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span]
    rfl
  simpa [coordinates,physicalCoordinates,hn] using hh

end SevenEighths.InverseInitialDyadicTailBound

end

end OAI
