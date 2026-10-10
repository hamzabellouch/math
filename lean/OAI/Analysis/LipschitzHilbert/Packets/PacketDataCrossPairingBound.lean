import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAdjointPairingBound
import OAI.Analysis.LipschitzHilbert.Trees.SourceOriginalIntegrability
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAdjointPolarization

namespace OAI

/-! Four exact polarized adjoint pairings control the distinct-profile
pairing with no loss in a common bound. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem cross_pairing_bound (P : PacketLatticeData N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l a k, planarProfileConstant (alt j l a k) (2*P.order)≤P.profileBound)
    (S : Finset P.PacketIndex) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, Measurable (b j l k)) (hb1 : ∀ j l k s, ‖b j l k s‖≤1)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (g f : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖≤1)
    (hf : MemLp f 2 (volume.prod volume)) (B : ℝ)
    (hbound : ∀ (c : ℂ) (hc : ‖c‖=1),
      ‖∫ z, inner ℂ ((P.polarize alt hAlt c hc).ordinaryAdjointSum S b u g z) (f z)
        ∂volume.prod volume‖≤B) :
    Integrable (fun z => inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q)
      (f z)) (volume.prod volume) ∧
      ‖∫ z, inner ℂ (∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q)
        (f z) ∂volume.prod volume‖≤B := by
  let A := (P.polarize alt hAlt 1 (by simp)).ordinaryAdjointSum S b u g
  let Bv := (P.polarize alt hAlt (-1) (by simp)).ordinaryAdjointSum S b u g
  let C := (P.polarize alt hAlt Complex.I (by simp)).ordinaryAdjointSum S b u g
  let D := (P.polarize alt hAlt (-Complex.I) (by simp)).ordinaryAdjointSum S b u g
  let X := fun z => ∑ q∈S, P.crossPacketValue alt hAlt 0 b u g z q
  have hA : Integrable (fun z => inner ℂ (A z) (f z)) (volume.prod volume) := integrable_euclidean_inner _
    ((P.polarize alt hAlt 1 (by simp)).ordinaryAdjointSum_memLp S b u g) hf
  have hB : Integrable (fun z => inner ℂ (Bv z) (f z)) (volume.prod volume) := integrable_euclidean_inner _
    ((P.polarize alt hAlt (-1) (by simp)).ordinaryAdjointSum_memLp S b u g) hf
  have hC : Integrable (fun z => inner ℂ (C z) (f z)) (volume.prod volume) := integrable_euclidean_inner _
    ((P.polarize alt hAlt Complex.I (by simp)).ordinaryAdjointSum_memLp S b u g) hf
  have hD : Integrable (fun z => inner ℂ (D z) (f z)) (volume.prod volume) := integrable_euclidean_inner _
    ((P.polarize alt hAlt (-Complex.I) (by simp)).ordinaryAdjointSum_memLp S b u g) hf
  refine ⟨integrable_euclidean_inner _ (P.crossSum_memLp alt hAlt 0 b u g 2 S) hf,?_⟩
  have hpoint (z : ℝ×ℝ) : (4:ℂ)*inner ℂ (X z) (f z)=
      inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
        Complex.I*inner ℂ (C z) (f z)-Complex.I*inner ℂ (D z) (f z) := by
    have h := congrArg (fun v => inner ℂ v (f z))
      (P.cross_adjoint_polarization alt hAlt S b hb hb1 u hu g hg hg1 z)
    simpa only [inner_smul_left,inner_add_left,inner_sub_left,map_ofNat,
      Complex.conj_I,neg_mul,sub_neg_eq_add,←sub_eq_add_neg] using h
  let ia := ∫ z, inner ℂ (A z) (f z) ∂volume.prod volume
  let ib := ∫ z, inner ℂ (Bv z) (f z) ∂volume.prod volume
  let ic := ∫ z, inner ℂ (C z) (f z) ∂volume.prod volume
  let idv := ∫ z, inner ℂ (D z) (f z) ∂volume.prod volume
  have hint : (4:ℂ)*(∫ z, inner ℂ (X z) (f z) ∂volume.prod volume)=
      ia-ib+Complex.I*ic-Complex.I*idv := by
    calc
      _ = ∫ z, (4:ℂ)*inner ℂ (X z) (f z) ∂volume.prod volume := (integral_const_mul _ _).symm
      _ = ∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
          Complex.I*inner ℂ (C z) (f z)-Complex.I*inner ℂ (D z) (f z)
          ∂volume.prod volume := integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = _ := by
        have hs : (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
            Complex.I*inner ℂ (C z) (f z)-Complex.I*inner ℂ (D z) (f z) ∂volume.prod volume)=
            (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
              Complex.I*inner ℂ (C z) (f z) ∂volume.prod volume)-
            (∫ z, Complex.I*inner ℂ (D z) (f z) ∂volume.prod volume) :=
          integral_sub ((hA.sub hB).add (hC.const_mul Complex.I)) (hD.const_mul Complex.I)
        have ha : (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z)+
            Complex.I*inner ℂ (C z) (f z) ∂volume.prod volume)=
            (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z) ∂volume.prod volume)+
            (∫ z, Complex.I*inner ℂ (C z) (f z) ∂volume.prod volume) :=
          integral_add (hA.sub hB) (hC.const_mul Complex.I)
        have hb : (∫ z, inner ℂ (A z) (f z)-inner ℂ (Bv z) (f z) ∂volume.prod volume)=ia-ib :=
          integral_sub hA hB
        rw [hs,ha,hb,integral_const_mul,integral_const_mul]
  have hnorm : 4*‖∫ z, inner ℂ (X z) (f z) ∂volume.prod volume‖≤
      ‖ia‖+‖ib‖+‖ic‖+‖idv‖ := by
    calc
      _ = ‖(4:ℂ)*(∫ z, inner ℂ (X z) (f z) ∂volume.prod volume)‖ := by
        rw [norm_mul]; norm_num
      _ = ‖ia-ib+Complex.I*ic-Complex.I*idv‖ := congrArg norm hint
      _ ≤ (‖ia‖+‖ib‖)+‖ic‖+‖idv‖ := by
        calc
          _ ≤ ‖ia-ib+Complex.I*ic‖+‖Complex.I*idv‖ := norm_sub_le _ _
          _ ≤ (‖ia-ib‖+‖Complex.I*ic‖)+‖Complex.I*idv‖ :=
            add_le_add (norm_add_le _ _) le_rfl
          _ ≤ ((‖ia‖+‖ib‖)+‖Complex.I*ic‖)+‖Complex.I*idv‖ := by
            gcongr; exact norm_sub_le _ _
          _ = _ := by simp only [norm_mul,Complex.norm_I,one_mul]
  have ha : ‖ia‖≤B := hbound 1 (by simp)
  have hb' : ‖ib‖≤B := hbound (-1) (by simp)
  have hc : ‖ic‖≤B := hbound Complex.I (by simp)
  have hd : ‖idv‖≤B := hbound (-Complex.I) (by simp)
  nlinarith

end LipschitzHilbert.PacketLatticeData

end

end OAI
