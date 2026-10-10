import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.SparseAmbient
import OAI.Probability.LatticeSurface.Coercivity.SparseColor
import OAI.Probability.LatticeSurface.Coercivity.SparseEntropy
import OAI.Probability.LatticeSurface.Coercivity.SparseGeodesic
import OAI.Probability.LatticeSurface.Coercivity.SparseGeometry
import OAI.Probability.LatticeSurface.Coercivity.SparseGradients
import OAI.Probability.LatticeSurface.Coercivity.SparseModel
import OAI.Probability.LatticeSurface.Coercivity.SparseParameters
import OAI.Probability.LatticeSurface.Coercivity.SparsePaths
import OAI.Probability.LatticeSurface.Coercivity.SparseProb
import OAI.Probability.LatticeSurface.Coercivity.SparseSeparated
import OAI.Probability.LatticeSurface.Coercivity.SparseWitnessModel
import OAI.Probability.LatticeSurface.Coercivity.ZeroPinnedSparse
import OAI.Probability.LatticeSurface.Convexity.BoundedBase
import OAI.Probability.LatticeSurface.Convexity.BrunnMinkowski
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.GradientWindows
import OAI.Probability.LatticeSurface.Convexity.ProductVolume
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.RetainedBody
import OAI.Probability.LatticeSurface.Convexity.RetainedCoordinates
import OAI.Probability.LatticeSurface.Convexity.RetainedShell
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality
import OAI.Probability.LatticeSurface.Geometry.BlockVolume
import OAI.Probability.LatticeSurface.Geometry.CapCentral
import OAI.Probability.LatticeSurface.Geometry.CapCompact
import OAI.Probability.LatticeSurface.Geometry.CapContract
import OAI.Probability.LatticeSurface.Geometry.CapCoordinates
import OAI.Probability.LatticeSurface.Geometry.CapMatching
import OAI.Probability.LatticeSurface.Geometry.CapOrient
import OAI.Probability.LatticeSurface.Geometry.CapReflection
import OAI.Probability.LatticeSurface.Geometry.CapSmall
import OAI.Probability.LatticeSurface.Geometry.CapSplit
import OAI.Probability.LatticeSurface.Geometry.CapUnpin
import OAI.Probability.LatticeSurface.Geometry.CapWeld
import OAI.Probability.LatticeSurface.Geometry.TriangularCover
import OAI.Probability.LatticeSurface.Geometry.TriangularGeometry
import OAI.Probability.LatticeSurface.Moments.ControlledGradients
import OAI.Probability.LatticeSurface.Moments.OrderedGradients

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

end FacetVolume

namespace ExtremalEdges

open scoped ENNReal

end ExtremalEdges

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*}

end ExtremalEdges

noncomputable section

namespace ExtremalEdges

open Finset

variable {V I : Type*} [Fintype V] [Fintype I]

attribute [local instance] Classical.propDecidable
local instance productDeficitDecidableEq₁ (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable
local instance productDeficitDecidableEq₂ (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

variable {V I : Type*} [Fintype V] [Fintype I]

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

end ExtremalEdges

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace TriangularLipschitz

end TriangularLipschitz

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace SparseBlocks

attribute [local instance] Classical.propDecidable

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable
local instance productDeficitDecidableEq₃ (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

noncomputable section

open scoped BigOperators

namespace SparsePaths

attribute [local instance] Classical.propDecidable
local instance productDeficitDecidableEq₄ (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparsePaths

noncomputable section

open scoped BigOperators

namespace SparseWitness

attribute [local instance] Classical.propDecidable
local instance productDeficitDecidableEq₅ (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseWitness

noncomputable section

open Set MeasureTheory

open scoped BigOperators

namespace SparseWitness

attribute [local instance] Classical.propDecidable
local instance productDeficitDecidableEq₆ (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseWitness

namespace SparseBlocks

attribute [local instance] Classical.propDecidable
local instance productDeficitDecidableEq₇ (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable
local instance productDeficitDecidableEq₈ (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

namespace SparseBlocks

open Filter

open scoped Topology

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable
local instance productDeficitDecidableEq₉ (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable
local instance productDeficitDecidableEq₁₀ (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

namespace SparseBlocks

attribute [local instance] Classical.propDecidable
local instance productDeficitDecidableEq₁₁ (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

end SparseBlocks

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

end RetainedShell

namespace ProductVolume

universe u v

variable {ι : Type u} [Fintype ι] {J : ι → Type v} [∀ i, Fintype (J i)]

end ProductVolume

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace SparseBlocks

end SparseBlocks

namespace RetainedShell

open TriangularLipschitz

attribute [local instance] Classical.propDecidable

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

noncomputable def realDensity (L : ℕ) (V J : Finset Vertex) (s : retained L V J → ℝ) : ℝ :=
  (shellDensity L V J s).toReal

noncomputable def shellDeficit (L : ℕ) (V J : Finset Vertex) (s χ : retained L V J → ℝ) (z : Vertex) : ℝ :=
  positiveLogVolume L (shellData L V J s z)-
    (positiveLogVolume L (shellData L V J (s+χ) z)+positiveLogVolume L (shellData L V J (s-χ) z))/2

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

lemma realDensity_product {L : ℕ} (hL : 0<L) (V J : Finset Vertex)
    (hf : ∀ z∈J,∀ x∈box L,base L z+x∈V) (s : retained L V J → ℝ) :
    realDensity L V J s=(remaining L V J).indicator
      (fun s => ∏ z:J,(fillingVolume L (shellData L V J s z)).toReal) s := by
  unfold realDensity
  rw [density_product L hL V J hf]
  by_cases hs : s∈remaining L V J
  · rw [Set.indicator_of_mem hs,Set.indicator_of_mem hs,ENNReal.toReal_prod]
  · simp [hs]

lemma positive_density_components {L : ℕ} (hL : 0<L) (V J : Finset Vertex)
    (hf : ∀ z∈J,∀ x∈box L,base L z+x∈V) (s : retained L V J → ℝ)
    (hs : 0<realDensity L V J s) : s∈remaining L V J ∧
    ∀ z∈J,0<fillingVolume L (shellData L V J s z) := by
  classical
  rw [realDensity_product hL V J hf] at hs
  have hr : s∈remaining L V J := by
    by_contra hh
    simp [hh] at hs
  rw [Set.indicator_of_mem hr] at hs
  refine ⟨hr,?_⟩
  intro z hz
  by_contra hh
  have hv : fillingVolume L (shellData L V J s z)=0 := le_antisymm (le_of_not_gt hh) zero_le
  have hprod : (∏ w:J,(fillingVolume L (shellData L V J s w)).toReal)=0 :=
    Finset.prod_eq_zero (i:=⟨z,hz⟩) (Finset.mem_univ _) (by simp [hv])
  rw [hprod] at hs
  exact lt_irrefl _ hs

lemma log_density_product {L : ℕ} (hL : 0<L) (V J : Finset Vertex)
    (hf : ∀ z∈J,∀ x∈box L,base L z+x∈V) (s : retained L V J → ℝ)
    (hs : 0<realDensity L V J s) :
    Real.log (realDensity L V J s)=∑ z∈J,positiveLogVolume L (shellData L V J s z) := by
  classical
  obtain ⟨hr,hv⟩ := positive_density_components hL V J hf s hs
  rw [realDensity_product hL V J hf,Set.indicator_of_mem hr,Real.log_prod]
  · simpa only [positiveLogVolume] using (Finset.sum_coe_sort J (fun z => Real.log (fillingVolume L (shellData L V J s z)).toReal))
  · intro z hz
    exact (ENNReal.toReal_pos (hv z z.2).ne' (fillingVolume_lt_top _ _).ne).ne'

end RetainedShell

namespace RetainedShell

open TriangularLipschitz

theorem overlap_product_identity {L : ℕ} (hL : 0<L) (V J : Finset Vertex)
    (hf : ∀ z∈J,∀ x∈box L,base L z+x∈V) (s χ : retained L V J → ℝ)
    (h0 : 0<realDensity L V J s) (hp : 0<realDensity L V J (s+χ))
    (hm : 0<realDensity L V J (s-χ)) :
    Real.sqrt (realDensity L V J (s+χ)*realDensity L V J (s-χ))=
      Real.exp (-(∑ z∈J,shellDeficit L V J s χ z))*realDensity L V J s := by
  have hg : (∑ z∈J,shellDeficit L V J s χ z)=Real.log (realDensity L V J s)-
      (Real.log (realDensity L V J (s+χ))+Real.log (realDensity L V J (s-χ)))/2 := by
    rw [log_density_product hL V J hf s h0,log_density_product hL V J hf (s+χ) hp,
      log_density_product hL V J hf (s-χ) hm]
    simp only [shellDeficit,Finset.sum_sub_distrib,← Finset.sum_div,← Finset.sum_add_distrib]
  rw [hg]
  have hprod := mul_pos hp hm
  have hlog : Real.log (Real.sqrt (realDensity L V J (s+χ)*realDensity L V J (s-χ)))=
      (Real.log (realDensity L V J (s+χ))+Real.log (realDensity L V J (s-χ)))/2 := by
    rw [Real.log_sqrt hprod.le,Real.log_mul hp.ne' hm.ne']
  rw [← hlog]
  rw [neg_sub,Real.exp_sub,Real.exp_log (Real.sqrt_pos.mpr hprod),Real.exp_log h0]
  exact (div_mul_cancel₀ _ h0.ne').symm

end RetainedShell

end
end
end
end
end
end
end

end OAI
