import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.BadClusters
import OAI.Probability.LatticeSurface.Coercivity.ConnectedPin
import OAI.Probability.LatticeSurface.Coercivity.DenseSpread
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.GridSpreadTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTrace
import OAI.Probability.LatticeSurface.Coercivity.GridTraceAnalytic
import OAI.Probability.LatticeSurface.Coercivity.GridTraceGeometry
import OAI.Probability.LatticeSurface.Coercivity.GridTraceKernel
import OAI.Probability.LatticeSurface.Coercivity.GridTraceMain
import OAI.Probability.LatticeSurface.Coercivity.GridTraceScale
import OAI.Probability.LatticeSurface.Coercivity.GridTraceTelescope
import OAI.Probability.LatticeSurface.Coercivity.HoleEdges
import OAI.Probability.LatticeSurface.Coercivity.HoleExtension
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleGoodEvent
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleLocal
import OAI.Probability.LatticeSurface.Coercivity.HoleMoments
import OAI.Probability.LatticeSurface.Coercivity.HolePointwise
import OAI.Probability.LatticeSurface.Coercivity.HoleSize
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HoleTail
import OAI.Probability.LatticeSurface.Coercivity.HullMore
import OAI.Probability.LatticeSurface.Coercivity.HullRims
import OAI.Probability.LatticeSurface.Coercivity.MomentBuffer
import OAI.Probability.LatticeSurface.Coercivity.MomentMarkov
import OAI.Probability.LatticeSurface.Coercivity.NaturalTailMoments
import OAI.Probability.LatticeSurface.Coercivity.OuterHulls
import OAI.Probability.LatticeSurface.Coercivity.PinSpread
import OAI.Probability.LatticeSurface.Coercivity.SparseClusters
import OAI.Probability.LatticeSurface.Coercivity.ThreeEvents
import OAI.Probability.LatticeSurface.Coercivity.TraceCoercivity
import OAI.Probability.LatticeSurface.Convexity.SoftThreshold
import OAI.Probability.LatticeSurface.Convexity.WeightedHolder
import OAI.Probability.LatticeSurface.Moments.CoercivityEnergy
import OAI.Probability.LatticeSurface.Moments.ScaledEnergy

namespace OAI

noncomputable section

open scoped BigOperators

namespace GridClosedLabels

end GridClosedLabels

namespace GridClosedLabels

end GridClosedLabels

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

open scoped BigOperators

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

open Classical

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

attribute [local instance] Classical.propDecidable

end SparseHoles

open scoped BigOperators

namespace SparseHoles

end SparseHoles

noncomputable section

open scoped BigOperators

namespace GridTrace

namespace NatGrid

end NatGrid

end GridTrace

namespace GridTrace.NatGrid

end GridTrace.NatGrid

namespace GridTrace.NatGrid

end GridTrace.NatGrid

namespace GridTrace.NatGrid

end GridTrace.NatGrid

noncomputable section

open scoped BigOperators

namespace GridTrace

end GridTrace

namespace GridTrace

end GridTrace

namespace GridTrace.NatGrid

end GridTrace.NatGrid

noncomputable section

open scoped BigOperators

namespace GridTrace

end GridTrace

namespace SparseHoles

end SparseHoles

namespace SparseHoles

attribute [local instance] Classical.propDecidable

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace GridTrace

end GridTrace

namespace GridTrace

end GridTrace

namespace GridTrace

end GridTrace

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

namespace SparseHoles

end SparseHoles

open Set MeasureTheory

namespace SparseClusters

variable {V : Type*} [Fintype V] [DecidableEq V]

end SparseClusters

namespace SparseClusters

variable {V : Type*} [Fintype V] [DecidableEq V]

end SparseClusters

namespace SparseHoles

open MeasureTheory

end SparseHoles

namespace SparseHoles

open MeasureTheory

attribute [local instance] Classical.propDecidable

end SparseHoles

namespace SparseHoles

open MeasureTheory

attribute [local instance] Classical.propDecidable

end SparseHoles

open MeasureTheory

open scoped NNReal ENNReal

namespace SparseHoles

end SparseHoles

namespace SparseHoles

open MeasureTheory

open scoped NNReal ENNReal

end SparseHoles

open MeasureTheory

open scoped NNReal ENNReal

namespace SparseHoles

end SparseHoles

open MeasureTheory

open scoped NNReal ENNReal

namespace SparseHoles

open MeasureTheory

open scoped NNReal ENNReal

end SparseHoles

namespace SparseHoles

open MeasureTheory

open scoped ENNReal NNReal

theorem average_coercivity (K M C R : ℝ) (hK : 0≤K) (hM : 0≤M)
    (hC : 1≤C) (hR : 1≤R) :
    ∃ C₀ C₁ : ℝ,0≤C₀ ∧ 0<C₁ ∧
    ∀ N : ℕ,1≤N → ∀ (w : Vertex → ℝ) (P : Finset Vertex),
    (∑ z∈GridTrace.square N,|w z|)≤C →
    (∀ z∈GridTrace.square N,|w z|≤C/(N:ℝ)^2) → P⊆GridTrace.square N →
    ((∑ z∈GridTrace.square N,w z)=0 ∨
      ((star.induce (P:Set Vertex)).Connected ∧ (N:ℝ)≤R*(diameter P:ℝ))) →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Finset Vertex) (B : Ω → Finset Vertex) (lo hi : Vertex),
    Measurable B → (∀ ω,B ω⊆A) → A⊆box lo hi →
    (∀ S : Finset Vertex,μ {ω | S⊆B ω}≤(1/1024:ENNReal)^S.card) →
    ∃ G : Set (Finset Vertex),(1/2:ENNReal)≤μ {ω | B ω∈G} ∧
      ∀ ω,B ω∈G → ∀ (X u : Vertex → ℝ),
        (∀ x y,grid.Adj x y → |X y-X x|≤K) →
        (u=X ∨ u=(fun z => softThreshold M (X z))) →
        ((∑ z∈GridTrace.square N,w z)=0 ∨ ∀ z∈P,u z=0) →
        |∑ z∈GridTrace.square N,w z*X z|≤
          C₀+C₁*(goodEnergy (holes (B ω) lo hi) N u)^(1/2:ℝ) := by
  classical
  obtain ⟨L,hL,hgood⟩ := hole_good_moment_event 12
  let D : ℝ := 145*L
  have hLp : 0<L := by linarith
  have hDp : 0<D := by dsimp [D];positivity
  let C' : ℝ := 4*(C+R+1)
  have hC' : 1≤C' := by dsimp [C'];linarith
  have hCC : C≤C' := by dsimp [C'];linarith
  have hRC : 2*R≤C' := by dsimp [C'];linarith
  obtain ⟨T,hT,htrace⟩ := GridTrace.trace_coercivity C' hC'
  obtain ⟨J,hJ,henergy⟩ := scaled_extension_energy D hDp
  let C₀ : ℝ := M*C'+6*K*C'*D
  let C₁ : ℝ := (1+C')*T*J
  have hCp : 0<C' := by linarith
  have hC₁ : 0<C₁ := by dsimp [C₁];positivity
  refine ⟨C₀,C₁,by dsimp [C₀];positivity,hC₁,?_⟩
  intro N hN w P hw hwd hPQ hgeometry Ω _ μ _ A B lo hi hB hBA hbox hsparse
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hw' : (∑ z∈GridTrace.square N,|w z|)≤C' := hw.trans hCC
  have hwd' : ∀ z∈GridTrace.square N,|w z|≤C'/(N:ℝ)^2 := by
    intro z hz
    exact (hwd z hz).trans (div_le_div_of_nonneg_right hCC (sq_nonneg _))
  have hdata (X u : Vertex → ℝ)
      (hX : ∀ x y,grid.Adj x y → |X y-X x|≤K)
      (hu : u=X ∨ u=(fun z => softThreshold M (X z))) :
      (∀ x y,grid.Adj x y → |u y-u x|≤K) ∧
      |(∑ z∈GridTrace.square N,w z*X z)-(∑ z∈GridTrace.square N,w z*u z)|≤M*C' := by
    have huL : ∀ x y,grid.Adj x y → |u y-u x|≤K := by
      rcases hu with rfl|rfl
      · exact hX
      · intro x y hxy
        exact (softThreshold_lipschitz M (X x) (X y) hM).trans (hX x y hxy)
    have he (z : Vertex) : |X z-u z|≤M := by
      rcases hu with rfl|rfl
      · simpa using hM
      · exact softThreshold_error M (X z) hM
    refine ⟨huL,?_⟩
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ z∈GridTrace.square N,|w z*X z-w z*u z| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z∈GridTrace.square N,|w z| * M := by
        apply Finset.sum_le_sum
        intro z hz
        rw [← mul_sub,abs_mul]
        exact mul_le_mul_of_nonneg_left (he z) (abs_nonneg _)
      _ = (∑ z∈GridTrace.square N,|w z|)*M := (Finset.sum_mul _ _ _).symm
      _ ≤ C'*M := mul_le_mul_of_nonneg_right hw' hM
      _ = _ := by ring
  by_cases hsmall : (N:ℝ)≤D
  · refine ⟨Set.univ,by simp,?_⟩
    intro ω hω X u hX hu hpin
    obtain ⟨huL,herr⟩ := hdata X u hX hu
    have hanchor : (∑ z∈GridTrace.square N,w z)=0 ∨ ∃ x∈GridTrace.square N,u x=0 := by
      by_cases hz : (∑ z∈GridTrace.square N,w z)=0
      · exact Or.inl hz
      · have hconn := (hgeometry.resolve_left hz).1
        obtain ⟨x⟩ := hconn.nonempty
        exact Or.inr ⟨x,hPQ x.property,(hpin.resolve_left hz) x x.property⟩
    have hbound := bounded_square_test N w u C' K hK hw' huL hanchor
    have hbound' : |∑ z∈GridTrace.square N,w z*u z|≤2*K*C'*D :=
      hbound.trans (mul_le_mul_of_nonneg_left hsmall (by positivity))
    have htri := abs_add_le ((∑ z∈GridTrace.square N,w z*X z)-(∑ z∈GridTrace.square N,w z*u z))
      (∑ z∈GridTrace.square N,w z*u z)
    rw [sub_add_cancel] at htri
    have he : 0≤(goodEnergy (holes (B ω) lo hi) N u)^(1/2:ℝ) :=
      Real.rpow_nonneg (goodEnergy_nonneg _ _ _) _
    calc
      _ ≤ M*C'+2*K*C'*D := by linarith
      _ ≤ C₀ := by dsimp [C₀];nlinarith [mul_nonneg (mul_nonneg hK hCp.le) hDp.le]
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hC₁.le he)
  have hlarge : D<(N:ℝ) := lt_of_not_ge hsmall
  have hνexists : ∃ ν : Vertex → ℝ,
      (∀ z,0≤ν z) ∧ (∑ z∈GridTrace.square N,ν z)≤1 ∧
      (∀ z r,0≤r → (∑ y∈GridTrace.ball N z r,ν y)≤C'*((r+1)/(N:ℝ))) ∧
      ((∑ z∈GridTrace.square N,w z)=0 ∨
        ((∑ z∈GridTrace.square N,ν z)=1 ∧ ∀ z,z∉P → ν z=0)) := by
    by_cases hz : (∑ z∈GridTrace.square N,w z)=0
    · refine ⟨fun _ => 0,by simp,by simp,?_,Or.inl hz⟩
      intro z r hr
      simp only [Finset.sum_const_zero]
      positivity
    · obtain ⟨ν,hν,hνP,hmass,hball⟩ := connected_pin_measure N hN P hPQ
        (hgeometry.resolve_left hz).1 R hR (hgeometry.resolve_left hz).2
      refine ⟨ν,hν,hmass.le,?_,Or.inr ⟨hmass,hνP⟩⟩
      intro z r hr
      exact (hball z r hr).trans (mul_le_mul_of_nonneg_right hRC (by positivity))
  obtain ⟨ν,hν,hνmass,hνball,hνanchor⟩ := hνexists
  let νn : Vertex → ℝ≥0 := fun z => ⟨ν z,hν z⟩
  obtain ⟨G,hG,hmom⟩ := hgood μ A B lo hi hB hBA hbox hsparse
    (GridTrace.square N) (GridTrace.square N) (incidentEdges (buffer N)) νn
  refine ⟨G,hG,?_⟩
  intro ω hω X u hX hu hpin
  obtain ⟨huL,herr⟩ := hdata X u hX hu
  obtain ⟨hsite,hedge,hanchor⟩ := hmom (B ω) hω
  let H := holes (B ω) lo hi
  have hH : HoleFamily H := outer_hole_family _ lo hi
    (badClusters_family _ lo hi ((hBA ω).trans hbox))
  have hsiteD : (∑ z∈GridTrace.square N,(siteDiameter H z+1:ℝ)^12)≤D*(N:ℝ)^2 := by
    calc
      _ ≤ L*((GridTrace.square N).card+1) := hsite
      _ ≤ L*(5*(N:ℝ)^2) := mul_le_mul_of_nonneg_left (square_card_bound N hN) hLp.le
      _ ≤ D*(N:ℝ)^2 := by dsimp [D];nlinarith [sq_nonneg (N:ℝ)]
  have hedgeD : (∑ e∈incidentEdges (buffer N),(edgeDiameter H e+1:ℝ)^12)≤D*(N:ℝ)^2 := by
    calc
      _ ≤ L*((incidentEdges (buffer N)).card+1) := hedge
      _ ≤ L*(145*(N:ℝ)^2) := mul_le_mul_of_nonneg_left (buffer_edges_bound N hN) hLp.le
      _ = _ := by dsimp [D];ring
  have hanchorD : (∑ z∈GridTrace.square N,ν z*(siteDiameter H z+1:ℝ))≤D := by
    calc
      _ ≤ L*((∑ z∈GridTrace.square N,ν z)+1) := hanchor
      _ ≤ L*(1+1) := mul_le_mul_of_nonneg_left (by linarith : (∑ z∈GridTrace.square N,ν z)+1≤1+1) hLp.le
      _ ≤ D := by dsimp [D];linarith
  have hd : ∀ z∈box (0,0) (N,N),siteDiameter H z≤N := moment_buffer N hN _ D hlarge hsiteD
  have hgrad := henergy H hH N hN hd hedgeD u
  have htraceAnchor : (∑ z∈GridTrace.square N,w z)=0 ∨
      ((∑ z∈GridTrace.square N,ν z)=1 ∧ ∀ z∈GridTrace.square N,ν z≠0 → u z=0) := by
    rcases hνanchor with hz|⟨hmass,hsup⟩
    · exact Or.inl hz
    · by_cases hz : (∑ z∈GridTrace.square N,w z)=0
      · exact Or.inl hz
      · refine Or.inr ⟨hmass,?_⟩
        intro z hzQ hνz
        have hzP : z∈P := by by_contra hn;exact hνz (hsup z hn)
        exact (hpin.resolve_left hz) z hzP
  have htest := htrace N hN w ν u (extension H u) (siteDiameter H) K D hK hDp.le
    hw' hwd' (fun z hz => hν z) hνmass (fun z hz r hr hrN => hνball z r hr)
    hsiteD hanchorD (fun z hz => by simpa only [add_comm] using filling_error H hH u K hK huL z) htraceAnchor
  have htest' : |∑ z∈GridTrace.square N,w z*u z|≤4*K*C'*D+
      C₁*(goodEnergy H N u)^(1/2:ℝ) := by
    calc
      _ ≤ 4*K*C'*D+(1+C')*T*((N:ℝ)^(-(1/3:ℝ))*(GridTrace.energy N (3/2) (extension H u))^(2/3:ℝ)) := by
        simpa only [mul_assoc] using htest
      _ ≤ 4*K*C'*D+(1+C')*T*(J*(goodEnergy H N u)^(1/2:ℝ)) :=
        by nlinarith [mul_le_mul_of_nonneg_left hgrad (show 0≤(1+C')*T by positivity)]
      _ = _ := by dsimp [C₁];ring
  have htri := abs_add_le ((∑ z∈GridTrace.square N,w z*X z)-(∑ z∈GridTrace.square N,w z*u z))
    (∑ z∈GridTrace.square N,w z*u z)
  rw [sub_add_cancel] at htri
  change _≤C₀+C₁*(goodEnergy H N u)^(1/2:ℝ)
  dsimp [C₀]
  nlinarith [mul_nonneg (mul_nonneg hK hCp.le) hDp.le]

end SparseHoles

end
end
end
end

end OAI
