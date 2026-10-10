import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairMixedReplacementCorrectedReindex
import OAI.NumberTheory.Ostmann.Arithmetic.MixedCellGridReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSmoothXi
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistorySymbolicEncoding InitialCoordinatesTemplate HistoryActiveCoordinates
open PrimeCellReplacement PrimeCellFreezing PrimeProgression LogCellPartition
open scoped BigOperators

theorem exists_correctedXi_mixed_grid_replacement_constants :
    ∃ d K L₀ : ℝ,0<d ∧ 0<K ∧ 1≤L₀ ∧
      ∀ (b s k₀ : ℕ) (X tb td G Δ E : ℝ) (center : ℕ→ℝ) (outside : List ℕ),
        0<X → (∀q∈outside,0<q) → outside.length=2*s →
      ∀ (l : ℕ) (V : ℕ→ℕ) (h k : History l)
        (hs : h.Supported V outside) (ks : k.Supported V outside),
        l≤k₀ → TreeSourceLabels (Template.initial (2*b) k₀) h →
        TreeSourceLabels (Template.initial (2*b) k₀) k →
      ∀ (τ : Type) (T U WH Wu : ℝ) (Hkeys Ukeys : List (PairKey h k))
        (S : Finset τ) (cellCenter : τ→ℝ) (cellKey : τ→PairKey h k),
      ∀ (I : Finset (PairKey h k)) (background : PairKey h k→ℝ),
        (∀i,0<background i) →
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (e : Option ι ≃ I)
        (NI : ℕ) (N : ι→ℕ) (M : ℕ) [NeZero M] (loI hiI ηI : ℝ) (lo hi η Z : ι→ℝ),
        loI≤hiI → 0<ηI → ⌊Real.exp hiI⌋₊≤NI →
        (∀i,L₀≤lo i ∧ lo i≤hi i ∧ 0<η i ∧ η i≤1 ∧
          ⌊Real.exp (hi i)⌋₊≤N i ∧ 0<Z i ∧ (M:ℝ)≤Real.exp (d*(lo i)^(1/3:ℝ))) →
        SourceBounds b k₀ G center h (leftMap h k) I background
          (fun j=>Option.elim' loI lo (e.symm j)) (fun j=>Option.elim' hiI hi (e.symm j)) →
        SourceBounds b k₀ G center k (rightMap h k) I background
          (fun j=>Option.elim' loI lo (e.symm j)) (fun j=>Option.elim' hiI hi (e.symm j)) →
        CounterpartBounds T U WH Wu Hkeys Ukeys I background
          (fun j=>Option.elim' loI lo (e.symm j)) (fun j=>Option.elim' hiI hi (e.symm j)) →
        Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
          (∑a,∑i,topCenters b center a i)+
          (∑a,∑j:Fin k₀,∑i,compensationCenters b center a j i) →
      ∀ ε B error mesh : ℝ,0≤ε → 1≤B → 0≤error → 0 ≤ mesh → ηI ≤ mesh → (∀i,η i ≤ mesh) →
        (∀(j:MixedGridIndex loI hiI ηI lo hi η) i,
          (K/Z i)*Real.exp (-d*(boxLower lo hi η j.2 i)^(1/3:ℝ))+
            (Z i*Real.exp (boxLower lo hi η j.2 i))⁻¹≤ε) →
        (∀(j:MixedGridIndex loI hiI ηI lo hi η) i,
          |harmonicIntegral M (boxLower lo hi η j.2 i) (boxUpper lo hi η j.2 i)/Z i|+
            ((K/Z i)*Real.exp (-d*(boxLower lo hi η j.2 i)^(1/3:ℝ))+
              (Z i*Real.exp (boxLower lo hi η j.2 i))⁻¹)≤B) →
        (∀j:MixedGridIndex loI hiI ηI lo hi η,
          mixedGridError (ι:=ι) M loI hiI ηI G 1 partitionDerivativeConstant smoothPartition ε B j.1≤error) →
      ∀F:ZMod M→(ι→(ZMod M)ˣ)→ℂ,
        let f := reindexedCorrectedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys S cellCenter cellKey I background e
        let v := ((Fintype.card ι:ℝ)+1)*correctedPairDerivativeBound WH Wu Hkeys.length Ukeys.length S.card h k V b k₀ tb Δ E center*mesh
        let A := Real.exp (WH+Wu)*Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k₀ E)
        ‖mixedSmoothTestSum NI N M loI hiI G smoothPartition lo hi Z F f-
            mixedPrincipalIntegral M loI hiI G smoothPartition lo hi Z f*
              ∑r:ZMod M,∑u:ι→(ZMod M)ˣ,F r u‖≤
          (2*v*mixedPrincipalMass M loI hiI G smoothPartition lo hi Z+
            (v+A)*(Fintype.card (MixedGridIndex loI hiI ηI lo hi η)*error))*
              ∑r:ZMod M,∑u:ι→(ZMod M)ˣ,‖F r u‖ := by
  obtain ⟨d,K,L₀,hd,hK,hL₀,hgrid⟩ := exists_mixed_grid_smooth_replacement_constants
  refine ⟨d,K,L₀,hd,hK,hL₀,?_⟩
  intro b s k₀ X tb td G Δ E center outside hX houtside hout l V h k hs ks hlk hl₁ hl₂
    τ T U WH Wu Hkeys Ukeys S cellCenter cellKey I background hbackground ι _ _ e NI N M _ loI hiI ηI lo hi η Z hI hηI hNI hcell
    hsrc₁ hsrc₂ hcorr hcenter ε B error mesh hε hB herror hm hmeshI hmesh hE hbound herr F
  have hφ : ∀t,HasDerivAt smoothPartition (deriv smoothPartition t) t :=
    fun t=>(smoothPartition_contDiff.differentiable (by simp) t).hasDerivAt
  apply hgrid ι NI N M loI hiI ηI G 1 partitionDerivativeConstant smoothPartition
    (deriv smoothPartition) lo hi η Z hI hηI hNI hφ
    (smoothPartition_contDiff.continuous_deriv (by simp))
    (fun t _=>smoothPartition_nonneg _) (fun t _=>by
      rw [abs_of_nonneg (smoothPartition_nonneg _)]; exact smoothPartition_le_one _)
    (fun t _=>partition_deriv_le_constant _) hcell ε B error hε hB herror hE hbound herr F
    (reindexedCorrectedRealXi b s X tb td G h k hs ks T U Hkeys Ukeys S cellCenter cellKey I background e)
    (correctedPairDerivativeBound WH Wu Hkeys.length Ukeys.length S.card h k V b k₀ tb Δ E center) mesh
    (Real.exp (WH+Wu)*Real.exp (-((2^l:ℕ):ℝ)*Δ+sourceXiConstant l k₀ E))
    (correctedPairDerivativeBound_nonneg WH Wu Hkeys.length Ukeys.length S.card h k V b k₀ tb Δ E center) hm hmeshI hmesh
  · intro z hz
    exact (reindexedCorrectedRealXi_log_contDiff b s X tb td G hX houtside h k hs ks
      T U Hkeys Ukeys S cellCenter cellKey I background hbackground e).differentiable (by simp) z
  · intro z hz i
    have hh := hcorr.log_products hbackground _ (reindex_mem_logRectangle e _ _ z hz)
    exact reindexedCorrectedRealXi_deriv_le b s k₀ X tb td G Δ E center hX houtside hout h k hs ks hlk hl₁ hl₂
      T U WH Wu Hkeys Ukeys S cellCenter cellKey I background hbackground e _ i
      (fun _=>Real.exp_pos _) hh.1 hh.2
      (hsrc₁.sourceDomain _ (reindex_mem_logRectangle e _ _ z hz))
      (hsrc₂.sourceDomain _ (reindex_mem_logRectangle e _ _ z hz)) hcenter
  · intro z hz
    have hh := hcorr.log_products hbackground _ (reindex_mem_logRectangle e _ _ z hz)
    exact correctedPairedRealXi_norm_le b s k₀ X tb td G Δ E center hX houtside hout h k hs ks
      T U WH Wu Hkeys Ukeys S cellCenter cellKey _
      (insert_positive I background _ hbackground (fun _=>Real.exp_pos _)) hh.1 hh.2
      (hsrc₁.sourceDomain _ (reindex_mem_logRectangle e _ _ z hz))
      (hsrc₂.sourceDomain _ (reindex_mem_logRectangle e _ _ z hz)) hcenter

end Ostmann.Arithmetic.HistoryPairSmoothXi

end

end OAI
