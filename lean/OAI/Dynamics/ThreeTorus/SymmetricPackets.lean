import OAI.Dynamics.ThreeTorus.TrackedPackets

namespace OAI

/-! Reflected neutral and signal producers, symmetric colors, physical control, and grouped cutoffs. -/

section

/-! The actual retained family, including its real compactly supported lifts,
preserves conjugation, with the literal inherited parent on its finite indices. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma retainedRealAmplitude_reflect (ψ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (s : ℝ) (j : ℤ) (a : UnitAddCircle) (x : ℝ) :
    retainedRealAmplitude ψ (fun s a => χ (-s) a) (-m) H (fun p => conj (A p)) s j a x =
      conj (retainedRealAmplitude ψ χ m H A (-s) (-j) a x) := by
  simp only [retainedRealAmplitude,retainedRealCore,exactPassageCoeff_neg,
    map_mul,Complex.conj_ofReal,fourier_neg]

def reflectedOutputIndex {ι : Type*} (τ : ι → ι) (S : ι → Finset ℤ)
    (hs : ∀ i j, j ∈ S (τ i) ↔ -j ∈ S i) : PassageOutputIndex S → PassageOutputIndex S :=
  fun i => ⟨τ i.1,⟨-i.2.val,(hs i.1 (-i.2.val)).mpr (by simpa only [neg_neg] using i.2.property)⟩⟩

lemma literal_output_reflection {ι : Type*} (F : PassagePackets ι)
    {τ : ι → ι} (hr : F.Reflection τ)
    (ψ : UnitAddCircle → ℝ) (ψ₀ : ℝ → ℝ) (χ : ι → ℝ → UnitAddCircle → ℝ)
    (H : ℕ → UnitAddCircle → UnitAddCircle) (n : ℕ) (S : ι → Finset ℤ)
    (hs : ∀ i j, j ∈ S (τ i) ↔ -j ∈ S i)
    (hχ : ∀ i s a, χ (τ i) s a = χ i (-s) a)
    (G : PassagePackets (PassageOutputIndex S))
    (hGm : ∀ i, G.m i = i.2.val)
    (hGA : ∀ i, G.A i = retainedAmplitude ψ (χ i.1) (F.m i.1) H (F.A i.1) n i.2.val)
    (hGA₀ : ∀ i, G.A₀ i = retainedRealAmplitude ψ₀ (χ i.1) (F.m i.1) (H n) (F.A i.1)
      ((i.2.val:ℝ)/n) i.2.val) :
    ∃ τG : PassageOutputIndex S → PassageOutputIndex S,
      (∀ i, (τG i).1 = τ i.1) ∧ G.Reflection τG := by
  let τG := reflectedOutputIndex τ S hs
  have hχ' i : χ (τ i) = fun s a => χ i (-s) a := funext (fun s => funext (hχ i s))
  have hA i : F.A (τ i) = fun p => conj (F.A i p) := funext (hr.amplitude i)
  refine ⟨τG,fun _ => rfl,⟨?_,?_,?_⟩⟩
  · intro i
    simp only [hGm,τG,reflectedOutputIndex]
  · intro i p
    rw [hGA,hGA]
    change retainedAmplitude ψ (χ (τ i.1)) (F.m (τ i.1)) H (F.A (τ i.1)) n (-i.2.val) p = _
    rw [hχ',hr.index,hA,retainedAmplitude_reflect,neg_neg]
  · intro i a x
    rw [hGA₀,hGA₀]
    change retainedRealAmplitude ψ₀ (χ (τ i.1)) (F.m (τ i.1)) (H n) (F.A (τ i.1))
      (((-i.2.val:ℤ):ℝ)/n) (-i.2.val) a x = _
    rw [hχ',hr.index,hA,retainedRealAmplitude_reflect]
    simp only [Int.cast_neg,neg_div,neg_neg]

lemma scalar_exact_indices_reflect {ι : Type*} {τ : ι → ι}
    {χ : ι → ℝ → ℝ} (hχ : ∀ i s, χ (τ i) s = χ i (-s))
    {S : ι → Finset ℤ} {n : ℕ} (he : ∀ i j, j ∈ S i ↔ χ i ((j:ℝ)/n) ≠ 0) :
    ∀ i j, j ∈ S (τ i) ↔ -j ∈ S i := by
  intro i j
  rw [he,he,hχ]
  simp only [Int.cast_neg,neg_div]

end ThreeTorus
end
end

section

/-! Full actual neutral producer, with conjugation of both amplitudes and
compact real lifts, inherited parent indices, and arbitrary final good arc. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

theorem eventually_neutral_anchor_reflected_family {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) (hi : Injective F.m) (hmod : F.SpareIndependent)
    {τref : ι → ι} (hr : F.Reflection τref)
    :
    ∀ᶠ c : ℕ in atTop, ∀ Q : ℕ, 0 < Q → ∀ ε τ κ : ℝ, 0 < ε → 0 < τ → 0 < κ →
      0 < c ∧ ∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ L : ℝ,
      ∃ χ : ι → ℝ → ℝ, ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ 0 < L ∧
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        χ i 0 = 0 ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        ∀ s ∈ tsupport (χ i), ∃ x ∈ F.core i,
          |s-(F.m i:ℝ)*((c:ℝ)+F.V x)| < τ) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, (c:ℝ)+F.V t)+Δ n*x):UnitAddCircle)) ∧
      let ψ := neutralCircleCutoff cut
      let J := neutralJitter cut L 0
      let J₀ := neutralJitterReal cut L 0
      let σ := fun (n : ℕ) a => (((1+J a/n)/n:ℝ):UnitAddCircle)
      (∀ n, Smooth (torusPassage (H n) (σ n)) ∧ Smooth (torusPassage (H n) (σ n)).symm ∧
        MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
      (∀ n, 0 < n → ∀ x : Cover,
        torusPassage (H n) (σ n) (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
        (torusPassage (H n) (σ n)).symm (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
      (∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ d : ℕ,
        TendstoUniformlyOn
          (fun (n : ℕ) x => iteratedFDeriv ℝ d
            (passageFamily (fun t => (c:ℝ)+F.V t) J₀ r ((n:ℝ)⁻¹,Δ n)) x)
          (fun x => iteratedFDeriv ℝ d (fun y : Cover => ![y 0+r*((c:ℝ)+F.V (y 1)),y 1,y 2]) x)
          atTop K) ∧
      ∃ S : ℕ → ι → Finset ℤ,
        (∀ n, 0 < n → Pairwise (fun i j => Disjoint (S n i) (S n j))) ∧
        (∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ χ i ((j:ℝ)/n) ≠ 0) ∧
        ∀ᶠ n : ℕ in atTop, 0 < n ∧
          (∀ i,
            let f := retainedPassage (F.m i) (H n) (F.A i) (S n i) (fun j _ => χ i ((j:ℝ)/n)) ψ
            let p := exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ (fun s _ => χ i s)
              (F.m i) H (F.A i) (S n i) n
            (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-f (passageChart (H n) x)‖^2
              ∂tripleVolume) < ε ∧
            (∫ z, |p z-F.density i z| ∂AddCircle.haarAddCircle) < ε ∧
            (∀ k : ℤ, (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter (σ n) k x) ∂tripleVolume) =
              ∫ z, (p z:ℂ)*fourier k z ∂AddCircle.haarAddCircle) ∧
            (∑ h : Fin Q, ∫ z,
              |exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ (fun s _ => χ i s) (F.m i) H (F.A i)
                ((S n i).filter (fun j => j % (Q:ℤ) = (h.val:ℤ) % (Q:ℤ))) n z-
                  (Q:ℝ)⁻¹*F.density i z| ∂AddCircle.haarAddCircle) < ε) ∧
          ∃ G : PassagePackets (PassageOutputIndex (S n)),
            Injective G.m ∧ G.SpareIndependent ∧
            G.V = (fun x => (1+J₀ x/n)/n) ∧
            (∀ i, G.m i = i.2.val) ∧
            (∀ i, G.A i = retainedAmplitude ψ (fun s _ => χ i.1 s) (F.m i.1) H (F.A i.1) n i.2.val) ∧
            (∀ i, G.density i = exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ
              (fun s _ => χ i.1 s) (F.m i.1) H (F.A i.1) {i.2.val} n) ∧
            (∀ i (E : ℤ → Prop) [DecidablePred E],
              exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ
                (fun s _ => χ i s) (F.m i) H (F.A i) ((S n i).filter E) n =
              fun z => ∑ j : ↥(S n i), if E j.val then G.density ⟨i,j⟩ z else 0) ∧
            ∃ τG : PassageOutputIndex (S n) → PassageOutputIndex (S n),
              (∀ i, (τG i).1 = τref i.1) ∧ G.Reflection τG ∧ G.GoodArc δ := by
  classical
  filter_upwards [eventually_integral_speed_separation F.m F.periodic.lift F.nonzero F.speed_continuous] with c hsep
  intro Q hQ ε τ κ hε hτ hκ
  obtain ⟨B,hB,hAB⟩ := F.amplitude_bound
  have hden : 0 < 32*(B+1) := by positivity
  obtain ⟨δ,hδ,hδall⟩ := exists_between (lt_min
    (lt_min (by norm_num : (0:ℝ)<1/8) (div_pos hε hden)) hκ)
  have hδhi := hδall.trans_le (min_le_left _ _)
  have hδκ := hδall.trans_le (min_le_right _ _)
  have hδ' : δ < 1/8 := hδhi.trans_le (min_le_left _ _)
  have hδB : 8*δ*B < ε/4 := by
    have hh := (lt_div_iff₀ hden).mp (hδhi.trans_le (min_le_right _ _))
    nlinarith
  let cut := lawCutoffs δ hδ hδ'
  obtain ⟨hcp,χ,hχ,hdisj,hχsym⟩ := tracked_symmetric_cutoffs_fixed_carrier F hi hmod hr hsep hτ
  let Fc := F.carrier (c:ℤ)
  let X : ι → ℝ → UnitAddCircle → ℝ := fun i s _ => χ i s
  have hXs i : CylinderSmooth (X i).uncurry := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => χ i p.1)
    exact (hχ i).1.comp contDiff_fst
  have hXc i : Continuous (X i).uncurry := (hχ i).1.continuous.comp continuous_fst
  have hXcompact i : HasCompactSupport (X i).uncurry := compactSupport_frequency_cylinder (hχ i).2.1
  have hXzero i (a : UnitAddCircle) : X i 0 a = 0 := (hχ i).2.2.1
  have hXbound i s (a : UnitAddCircle) : 0 ≤ X i s a ∧ X i s a ≤ 1 := (hχ i).2.2.2.1 s
  have hXW i s a : stationaryWeight (Icc (Fc.l-Fc.R) (Fc.u+Fc.R))
      (fun x => (Fc.m i:ℝ)*Fc.V x) (Fc.A₀ i a) s ≠ 0 → X i s a = 1 := by
    simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using
      (hχ i).2.2.2.2.2 (Icc (F.l-F.R) (F.u+F.R)) a s
  have hzero i : 0 ∉ (fun x => (Fc.m i:ℝ)*Fc.V x) '' Icc Fc.l Fc.u := by
    rintro ⟨x,_hx,he⟩
    apply hsep.2.1 i (x:UnitAddCircle)
    change (F.m i:ℝ)*((c:ℝ)+F.V x) = 0
    simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using he
  obtain ⟨Δ,H,hΔ,hΔt,hHc,hHe,C,Cq,_hC,_hCq,hrest⟩ :=
    exists_simultaneous_neutral_residue_passage Fc.nonzero Fc.lift_matches Fc.two Fc.continuous_lift
      Fc.continuous_deriv Fc.smooth_lift Fc.support_lift Fc.lo Fc.uo Fc.lu Fc.Rpos
      Fc.periodic Fc.smooth_speed Fc.positive_deriv hzero Fc.continuous_amplitude Fc.smooth_amplitude
      (B := fun _ => B) (fun _ => hB) hAB cut hδ hδ' hXs hXc hXcompact hXzero hXbound hXW hQ
  have hsmall : 0 < ε/4 := by positivity
  have hCT i : ∀ᶠ L : ℝ in atTop, C i/L < ε/4 :=
    (tendsto_const_nhds.div_atTop tendsto_id).eventually (gt_mem_nhds hsmall)
  have hCqT i : ∀ᶠ L : ℝ in atTop, Cq i/L < ε/4 :=
    (tendsto_const_nhds.div_atTop tendsto_id).eventually (gt_mem_nhds hsmall)
  obtain ⟨L,hL,hCL,hCqL⟩ := ((eventually_gt_atTop (0:ℝ)).and
    (((Filter.eventually_all).mpr hCT).and ((Filter.eventually_all).mpr hCqT))).exists
  obtain ⟨hgeo,hgraph,hlimit,S,hSN,_hST,hTE,hgood⟩ := hrest L hL 0
  have hTE' n (hn : 0 < n) i j : j ∈ S n i ↔ χ i ((j:ℝ)/n) ≠ 0 := by
    simpa only [X,exists_const] using hTE n hn i j
  have hSd n (hn : 0 < n) : Pairwise (fun i j => Disjoint (S n i) (S n j)) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro k hki hkj
    exact Set.disjoint_left.mp (hdisj hij)
      (subset_tsupport _ ((hTE' n hn i k).mp hki)) (subset_tsupport _ ((hTE' n hn j k).mp hkj))
  refine ⟨hcp,δ,cut,L,χ,Δ,H,hδ,hδ',hδκ,hL,?_,hdisj,hΔ,hΔt,hHc,?_,?_,?_,?_,S,hSd,hTE',?_⟩
  · exact fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1,(hχ i).2.2.2.1,(hχ i).2.2.2.2.1⟩
  · simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using hHe
  · exact hgeo
  · simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using hgraph
  · simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using hlimit
  filter_upwards [hgood (ε/4) hsmall] with n hn
  have hn0 := hn.1
  refine ⟨hn0,?_,?_⟩
  · intro i
    have hh := hn.2 i
    dsimp only at hh ⊢
    have hPM := (Fc.density_marginal (F.carrier_spare (c:ℤ) hmod) i).trans
      (F.density_carrier hmod (c:ℤ) i)
    rw [hPM] at hh
    refine ⟨lt_trans hh.1 (by linarith), lt_trans hh.2.1 (by linarith [hCL i]),
      hh.2.2.2.1,lt_trans hh.2.2.2.2.2 (by linarith [hCqL i])⟩
  · let Hl (n : ℕ) (x : ℝ) := (n:ℝ)*((∫ t in 0..x, Fc.V t)+Δ n*x)
    have hHl n : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n) :=
      contDiff_const.mul ((contDiff_real_primitive Fc.smooth_speed).add (contDiff_const.mul contDiff_id))
    have hJs := neutralJitterReal_smooth cut L 0
    have hJd x (hx : x ∈ Ioo δ (1-δ)) : 0 < deriv (neutralJitterReal cut L 0) x := by
      rw [neutralJitterReal_deriv cut hδ L 0 hx]
      exact hL
    obtain ⟨G,hGm,hGA,hGA₀,hGV,hGo,hGl,hGu,hGmod⟩ := literal_output_packets
      F.m F.A H Hl X (S n) (hSN n hn0) F.continuous_amplitude F.smooth_amplitude
      hXs hXc hHc hHl hHe cut hδ hδ' (neutralJitterReal_periodic cut L 0) hJs hJd hn0
    have heψ : ∀ x ∈ Ioc (0:ℝ) (0+1), neutralCircleCutoff cut (x:UnitAddCircle) = cut.ψ x := by
      intro x hx
      rw [neutralCircleCutoff_coe]
      exact periodize_eq_on_unit ((subset_tsupport cut.ψ).trans
        (cut.ψ_support.trans (by intro z hz; constructor <;> linarith [hz.1,hz.2]))) ⟨hx.1.le,by simpa using hx.2⟩
    have hsψ : tsupport cut.ψ ⊆ Ioc (0:ℝ) (0+1) ∩ Ioo δ (1-δ) := by
      intro x hx
      have hh := cut.ψ_support hx
      exact ⟨⟨by linarith [hh.1],by linarith [hh.2]⟩,hh⟩
    have hJinj : InjOn (neutralJitterReal cut L 0) (Ioo δ (1-δ)) := by
      intro x hx y hy he
      rw [neutralJitterReal_affine cut hδ L 0 ⟨hx.1.le,hx.2.le⟩,
        neutralJitterReal_affine cut hδ L 0 ⟨hy.1.le,hy.2.le⟩] at he
      nlinarith
    have hGden (i : PassageOutputIndex (S n)) : G.density i =
        exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal cut L 0) (neutralCircleCutoff cut)
          (X i.1) (F.m i.1) H (F.A i.1) {i.2.val} n := by
      apply literal_packet_canonical_density G hGmod i (hGm i) (hGA i) ?_
        (continuous_neutralJitter cut L 0) hJs (fun _ _ => rfl) isOpen_Ioo hJinj
        (fun x hx => (hJd x hx).ne') (continuous_neutralCircleCutoff cut) cut.ψ_smooth cut.ψ_compact
        heψ hsψ (hXc i.1) (hXs i.1) hHc hHl hHe (F.continuous_amplitude i.1)
        (F.smooth_amplitude i.1) hn0
      intro a
      obtain ⟨x,rfl⟩ := Quotient.mk_surjective a
      change (G.V x:UnitAddCircle) = _
      rw [hGV]
      rfl
    refine ⟨G,?_,hGmod,hGV,hGm,hGA,hGden,?_,?_⟩
    · have he : G.m = fun i : PassageOutputIndex (S n) => i.2.val := funext hGm
      rw [he]
      exact output_index_injective (hSd n hn0)
    · intro i E inst
      simp_rw [hGden]
      exact exactRetainedPacketDensity_filtered_singletons hJs isOpen_Ioo hJinj
        (fun x hx => (hJd x hx).ne') cut.ψ_smooth cut.ψ_compact heψ hsψ (hXs i)
        hHl hHe (F.smooth_amplitude i) hn0 (hSN n hn0 i) E

    · obtain ⟨τG,hτG,hrG⟩ := literal_output_reflection F hr (neutralCircleCutoff cut) cut.ψ X H n (S n)
        (scalar_exact_indices_reflect hχsym (hTE' n hn0)) (fun i s _ => hχsym i s)
        G hGm hGA hGA₀
      refine ⟨τG,hτG,hrG,hGo,hGl,hGu,?_⟩
      intro x hx
      rw [hGV]
      exact positive_deriv_new_speed hn0 (hJd x hx)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

theorem exists_neutral_reflected_tracked_family {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) (hi : Injective F.m) (hmod : F.SpareIndependent)
    {τref : ι → ι} (hr : F.Reflection τref)
    {B D ε η κ : ℝ} (hB : 0 < B) (hD : ∀ i, |(F.m i:ℝ)/B| ≤ D)
    (hε : 0 < ε) (hη : 0 < η) (hκ : 0 < κ) {Q : ℕ} [NeZero Q] (hQ : 0 < Q) :
    ∃ c : ℕ, 0 < c ∧ ∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ L : ℝ,
      ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ 0 < L ∧
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, (c:ℝ)+F.V t)+Δ n*x):UnitAddCircle)) ∧
      let J := neutralJitter cut L 0
      let J₀ := neutralJitterReal cut L 0
      let σ := fun (n : ℕ) a => (((1+J a/n)/n:ℝ):UnitAddCircle)
      (∀ n, Smooth (torusPassage (H n) (σ n)) ∧ Smooth (torusPassage (H n) (σ n)).symm ∧
        MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
      (∀ n, 0 < n → ∀ x : Cover,
        torusPassage (H n) (σ n) (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
        (torusPassage (H n) (σ n)).symm (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
      (∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ d : ℕ,
        TendstoUniformlyOn
          (fun (n : ℕ) x => iteratedFDeriv ℝ d
            (passageFamily (fun t => (c:ℝ)+F.V t) J₀ r ((n:ℝ)⁻¹,Δ n)) x)
          (fun x => iteratedFDeriv ℝ d (fun y : Cover => ![y 0+r*((c:ℝ)+F.V (y 1)),y 1,y 2]) x)
          atTop K) ∧
      ∃ S : ℕ → ι → Finset ℤ, ∀ᶠ n : ℕ in atTop, 0 < n ∧
        ∃ G : PassagePackets (PassageOutputIndex (S n)),
          Injective G.m ∧ G.SpareIndependent ∧
          G.V = (fun x => (1+J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
          (∀ i,
            (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
              outputVector G i (passageChart (H n) x)‖^2 ∂tripleVolume) < ε ∧
            (∫ z, |outputDensity G i z-F.density i z| ∂phaseHaar) < ε ∧
            (∑ h : Fin Q, ∫ z,
              |(∑ j : ↥(S n i), if signalResidue Q j.val = h then G.density ⟨i,j⟩ z else 0)-
                  (Q:ℝ)⁻¹*F.density i z| ∂phaseHaar) < ε) ∧
          (∀ i, ∃ x ∈ F.core i.1,
            |(G.m i:ℝ)/((n:ℝ)*c*B)-(F.m i.1:ℝ)/B| < η ∧
            ∀ y, dist ((G.m i:ℝ)*G.V y:UnitAddCircle)
              ((F.m i.1:ℝ)*F.V x:UnitAddCircle) < η) ∧
          ∃ τG : PassageOutputIndex (S n) → PassageOutputIndex (S n),
            (∀ i, (τG i).1 = τref i.1) ∧ G.Reflection τG ∧ G.GoodArc δ := by
  classical
  obtain ⟨P,_hP,hPV⟩ := F.speed_bound
  obtain ⟨M,_hM,hMm⟩ := F.angular_bound
  let τ := η/4
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτη : τ < η/2 := by dsimp [τ]; linarith
  have hraw := (eventually_neutral_anchor_reflected_family F hi hmod hr).mono
    (fun _ hc => hc Q hQ ε τ κ hε hτ hκ)
  obtain ⟨c,hc,hbud⟩ := (hraw.and
    (support_drift_budgets (D := D) (P := P) (M := M) hB hη)).exists
  obtain ⟨hcp,δ,cut,L,χ,Δ,H,hδ,hδ',hδκ,hL,hχ,_hχd,hΔ,hΔt,hHc,hHe,hgeo,hgraph,hlimit,S,_hSd,hS,hgood⟩ := hc
  have hb := hbud.2 τ hτ hτη
  obtain ⟨R,_hR,hRJ⟩ := periodic_real_bound (neutralJitterReal_smooth cut L 0).continuous
    (neutralJitterReal_periodic cut L 0)
  refine ⟨c,hcp,δ,cut,L,Δ,H,hδ,hδ',hδκ,hL,hΔ,hΔt,hHc,hHe,hgeo,hgraph,hlimit,S,?_⟩
  filter_upwards [hgood,hb.2 R] with n hn hnb
  obtain ⟨hnp,haul,G,hGi,hGmod,hGV,hGm,hGA,_hGden,hgroup,hreflect⟩ := hn
  refine ⟨hnp,G,hGi,hGmod,hGV,hGm,?_,?_,hreflect⟩
  · intro i
    have hv := outputVector_eq_retained F G (neutralCircleCutoff cut) (fun i s _ => χ i s)
      H n hGm hGA i
    have hp : exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal cut L 0)
        (neutralCircleCutoff cut) (fun s _ => χ i s) (F.m i) H (F.A i) (S n i) n =
        outputDensity G i := by
      have hh := hgroup i (fun _ => True)
      change _ = fun z => ∑ j : ↥(S n i), G.density ⟨i,j⟩ z
      simpa only [Finset.filter_true,ite_true] using hh
    have hr (h : Fin Q) : exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal cut L 0)
        (neutralCircleCutoff cut) (fun s _ => χ i s) (F.m i) H (F.A i)
          ((S n i).filter (fun j => j % (Q:ℤ) = (h.val:ℤ) % (Q:ℤ))) n =
        (fun z => ∑ j : ↥(S n i), if signalResidue Q j.val = h then G.density ⟨i,j⟩ z else 0) := by
      rw [hgroup]
      funext z
      apply Finset.sum_congr rfl
      intro j _
      simp only [signalResidue_eq_iff Q]
    have hh := haul i
    dsimp only at hh
    rw [← hv,hp] at hh
    simp_rw [hr] at hh
    exact ⟨hh.1,hh.2.1,hh.2.2.2⟩
  · intro i
    obtain ⟨x,hx,ha,ht⟩ := literal_output_tracking hcp hnp hB hD hPV hMm hRJ
      (fun i j hj => (hS n hnp i j).mp hj) (fun i => (hχ i).2.2.2.2) hGm hGV i
    exact ⟨x,hx,ha.trans_lt hb.1,fun y => (ht y).trans_lt hnb.2⟩

end ThreeTorus
end
end

section

/-! Uniform-before-all-future-packet-types signal producer, with actual
conjugate amplitudes and compact lifts preserved, not only model symmetry. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
universe u

theorem exists_signal_state_reflected_family
    {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ α : ℝ, ∃ L : ℕ, ∃ γ₀ : ℝ,
      0 < α ∧ α < b/2 ∧ 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (ι : Type u) [Fintype ι], ∀ (F : PassagePackets ι),
      Injective F.m → F.SpareIndependent → ∀ τref : ι → ι, F.Reflection τref → ∀ B : ℝ, 0 < B →
      (∀ i, b ≤ |(F.m i:ℝ)/B|) →
      ∀ ε τ κ : ℝ, 0 < ε → 0 < τ → 0 < κ →
      ∀ᶠ c : ℕ in atTop, 0 < c ∧
      ∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ χ : ι → ℝ → ℝ,
      ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      0 < δ ∧ δ < 1/8 ∧ δ < κ ∧
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        χ i 0 = 0 ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        ∀ s ∈ tsupport (χ i), ∃ x ∈ F.core i,
          |s-(F.m i:ℝ)*((c:ℝ)+F.V x)| < τ) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, (c:ℝ)+F.V t)+Δ n*x):UnitAddCircle)) ∧
      let ρ := signalJitter α γ d (signalPrimeProduct L) B c
      let ψ := neutralCircleCutoff cut
      let J := quantileCircleJitter ρ cut
      let J₀ := lawJitter ρ cut
      let σ := fun (n : ℕ) a => (((1+J a/n)/n:ℝ):UnitAddCircle)
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ Integrable ρ ∧
      (∀ y, 0 < ρ y) ∧ (∫ y, ρ y = 1) ∧
      (∀ n, Smooth (torusPassage (H n) (σ n)) ∧ Smooth (torusPassage (H n) (σ n)).symm ∧
        MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
      (∀ n, 0 < n → ∀ x : Cover,
        torusPassage (H n) (σ n) (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
        (torusPassage (H n) (σ n)).symm (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
      (∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ e : ℕ,
        TendstoUniformlyOn
          (fun (n : ℕ) x => iteratedFDeriv ℝ e
            (passageFamily (fun t => (c:ℝ)+F.V t) J₀ r ((n:ℝ)⁻¹,Δ n)) x)
          (fun x => iteratedFDeriv ℝ e (fun y : Cover => ![y 0+r*((c:ℝ)+F.V (y 1)),y 1,y 2]) x)
          atTop K) ∧
      ∃ S : ℕ → ι → Finset ℤ,
        (∀ n, 0 < n → Pairwise (fun i j => Disjoint (S n i) (S n j))) ∧
        (∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ χ i ((j:ℝ)/n) ≠ 0) ∧
        ∀ᶠ n : ℕ in atTop, 0 < n ∧
          (∀ i,
            let f := retainedPassage (F.m i) (H n) (F.A i) (S n i) (fun j _ => χ i ((j:ℝ)/n)) ψ
            let p := exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ (fun s _ => χ i s)
              (F.m i) H (F.A i) (S n i) n
            (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-f (passageChart (H n) x)‖^2
              ∂tripleVolume) < ε ∧
            (∫ z, |p z-F.density i z*signalCircleModel (signalPrimeProduct L) γ B d
              (F.m i) ((n:ℤ) • z)| ∂AddCircle.haarAddCircle) < ε ∧
            (∀ k : ℤ, (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter (σ n) k x) ∂tripleVolume) =
              ∫ z, (p z:ℂ)*fourier k z ∂AddCircle.haarAddCircle)) ∧
          ∃ G : PassagePackets (PassageOutputIndex (S n)),
            Injective G.m ∧ G.SpareIndependent ∧
            G.V = (fun x => (1+J₀ x/n)/n) ∧
            (∀ i, G.m i = i.2.val) ∧
            (∀ i, G.A i = retainedAmplitude ψ (fun s _ => χ i.1 s) (F.m i.1) H (F.A i.1) n i.2.val) ∧
            (∀ i, G.density i = exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ
              (fun s _ => χ i.1 s) (F.m i.1) H (F.A i.1) {i.2.val} n) ∧
            (∀ i (E : ℤ → Prop) [DecidablePred E],
              exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ
                (fun s _ => χ i s) (F.m i) H (F.A i) ((S n i).filter E) n =
              fun z => ∑ j : ↥(S n i), if E j.val then G.density ⟨i,j⟩ z else 0) ∧
            ∃ τG : PassageOutputIndex (S n) → PassageOutputIndex (S n),
              (∀ i, (τG i).1 = τref i.1) ∧ G.Reflection τG ∧ G.GoodArc δ := by
  classical
  obtain ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,hγ⟩ := exists_actual_signal_family hb hbD hd hdc hdr hd0 hds
  refine ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,?_⟩
  intro γ hγp hγs
  obtain ⟨hdb,hsignal⟩ := hγ γ hγp hγs
  refine ⟨hdb,?_⟩
  intro ι inst F hi hmod τref hr B hB hm ε τ κ hε hτ hκ
  obtain ⟨M,hM,hAM⟩ := F.amplitude_bound
  obtain ⟨W,hW,hWM⟩ := F.weight_mass_bound
  let K := M+W+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hMK : M ≤ K := by dsimp [K]; linarith
  have hWK : W ≤ K := by dsimp [K]; linarith
  let ε₀ := ε/(8*K)
  have hε₀ : 0 < ε₀ := div_pos hε (by positivity)
  obtain ⟨δ,hδ,hδall⟩ := exists_between (lt_min (lt_min (by norm_num : (0:ℝ)<1/8)
    (div_pos hε (show 0 < 32*K by positivity))) hκ)
  have hδhi := hδall.trans_le (min_le_left _ _)
  have hδκ := hδall.trans_le (min_le_right _ _)
  have hδ' : δ < 1/8 := hδhi.trans_le (min_le_left _ _)
  have hδK : 32*δ*K < ε := by
    have hh := (lt_div_iff₀ (show 0 < 32*K by positivity)).mp (hδhi.trans_le (min_le_right _ _))
    nlinarith
  have hδM : 8*δ*M < ε/4 := by nlinarith [mul_le_mul_of_nonneg_left hMK hδ.le]
  have hε₀K : ε₀*K = ε/8 := by dsimp [ε₀]; field_simp
  have hcoef : 0 ≤ 4*δ+ε₀ := by positivity
  have hCK : K*(4*δ+ε₀) < ε/4 := by nlinarith
  let cut := lawCutoffs δ hδ hδ'
  have hsignal' := hsignal ι B hB F.m hm F.A F.A₀ F.V F.o F.l F.u F.R
    F.lift_matches F.two F.continuous_lift F.continuous_deriv F.smooth_lift F.support_lift
    F.lo F.uo F.lu F.Rpos F.periodic F.smooth_speed F.positive_deriv
    F.continuous_amplitude F.smooth_amplitude hmod.1 hmod.2 ε₀ hε₀
  filter_upwards [eventually_integral_speed_separation F.m F.periodic.lift F.nonzero F.speed_continuous,hsignal'] with c hc hs
  obtain ⟨hcp,χ,hχ,hdisj,hχsym⟩ := tracked_symmetric_cutoffs_fixed_carrier F hi hmod hr hc hτ
  let Fc := F.carrier (c:ℤ)
  let X : ι → ℝ → UnitAddCircle → ℝ := fun i s _ => χ i s
  have hXs i : CylinderSmooth (X i).uncurry := by
    change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => χ i p.1)
    exact (hχ i).1.comp contDiff_fst
  have hXc i : Continuous (X i).uncurry := (hχ i).1.continuous.comp continuous_fst
  have hXcompact i : HasCompactSupport (X i).uncurry := compactSupport_frequency_cylinder (hχ i).2.1
  have hXzero i (a : UnitAddCircle) : X i 0 a = 0 := (hχ i).2.2.1
  have hXbound i s (a : UnitAddCircle) : 0 ≤ X i s a ∧ X i s a ≤ 1 := (hχ i).2.2.2.1 s
  have hXW i s a : stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
      (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i a) s ≠ 0 → X i s a = 1 :=
    (hχ i).2.2.2.2.2 _ a s
  obtain ⟨hρs,hρi,hρp,hρm,Δ,H,hΔ,hΔt,hHc,hHe,hgeo,hgraph,hlimit,S,hSN,_hST,hTE,hgood⟩ :=
    hs.2.2 δ cut hδ hδ' X hXs hXc hXcompact hXzero hXbound hXW
  have hTE' n (hn : 0 < n) i j : j ∈ S n i ↔ χ i ((j:ℝ)/n) ≠ 0 := by
    simpa only [X,exists_const] using hTE n hn i j
  have hSd n (hn : 0 < n) : Pairwise (fun i j => Disjoint (S n i) (S n j)) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro k hki hkj
    exact Set.disjoint_left.mp (hdisj hij)
      (subset_tsupport _ ((hTE' n hn i k).mp hki)) (subset_tsupport _ ((hTE' n hn j k).mp hkj))
  refine ⟨hcp,δ,cut,χ,Δ,H,hδ,hδ',hδκ,?_,hdisj,hΔ,hΔt,hHc,hHe,hρs,hρi,hρp,hρm,hgeo,hgraph,hlimit,S,hSd,hTE',?_⟩
  · exact fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1,(hχ i).2.2.2.1,(hχ i).2.2.2.2.1⟩
  have hsmall : 0 < ε/4 := by positivity
  filter_upwards [hgood (ε/4) hsmall] with n hn
  have hn0 := hn.1
  refine ⟨hn0,?_,?_⟩
  · intro i
    have hh := hn.2 i
    dsimp only at hh ⊢
    have hden : foldCircleDensity (stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
        (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i 0)) = F.density i := by
      simpa only [Fc,PassagePackets.carrier,Int.cast_natCast,PassagePackets.density,
        PassagePackets.weight] using F.density_carrier hmod (c:ℤ) i
    have hmass : (∫ s, stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
        (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i 0) s)*(4*δ+ε₀) < ε/4 := by
      have he := F.weight_mass_carrier hmod (c:ℤ) i
      dsimp only [PassagePackets.weight,PassagePackets.carrier] at he
      simp only [Int.cast_natCast] at he
      rw [he]
      exact (mul_le_mul_of_nonneg_right ((hWM i).trans hWK) hcoef).trans_lt hCK
    have hAint : Integrable (fun u : UnitAddCircle => ‖F.A i (u,0)‖^2) AddCircle.haarAddCircle :=
      (((F.continuous_amplitude i).comp (continuous_id.prodMk continuous_const)).norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hMint : (∫ u, ‖F.A i (u,0)‖^2 ∂AddCircle.haarAddCircle) ≤ M := by
      calc
        _ ≤ ∫ _u : UnitAddCircle, M ∂AddCircle.haarAddCircle := integral_mono hAint (integrable_const _) (fun u => hAM i (u,0))
        _ = M := by simp
    rw [hden] at hh
    refine ⟨lt_trans hh.1 ?_,lt_trans hh.2.1 (by linarith),hh.2.2.2.1⟩
    have hhM := mul_le_mul_of_nonneg_left hMint (show 0 ≤ 8*δ by positivity)
    linarith
  · let ρ := signalJitter α γ d (signalPrimeProduct L) B c
    let Hl (n : ℕ) (x : ℝ) := (n:ℝ)*((∫ t in 0..x, (c:ℝ)+F.V t)+Δ n*x)
    have hHl n : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n) :=
      contDiff_const.mul ((contDiff_real_primitive (contDiff_const.add F.smooth_speed)).add
        (contDiff_const.mul contDiff_id))
    have hJs := lawJitter_smooth cut hρs hρi hρp hρm
    have hJd x (hx : x ∈ Ioo δ (1-δ)) : 0 < deriv (lawJitter ρ cut) x := by
      obtain ⟨he,hp⟩ := lawJitter_deriv_pos cut hρs hρi hρp hρm hδ hx
      rwa [he.deriv]
    obtain ⟨G,hGm,hGA,hGA₀,hGV,hGo,hGl,hGu,hGmod⟩ := literal_output_packets
      F.m F.A H Hl X (S n) (hSN n hn0) F.continuous_amplitude F.smooth_amplitude
      hXs hXc hHc hHl hHe cut hδ hδ' (periodize_periodic _) hJs hJd hn0
    have heψ : ∀ x ∈ Ioc (0:ℝ) (0+1), neutralCircleCutoff cut (x:UnitAddCircle) = cut.ψ x := by
      intro x hx
      rw [neutralCircleCutoff_coe]
      exact periodize_eq_on_unit ((subset_tsupport cut.ψ).trans
        (cut.ψ_support.trans (by intro z hz; constructor <;> linarith [hz.1,hz.2]))) ⟨hx.1.le,by simpa using hx.2⟩
    have hsψ : tsupport cut.ψ ⊆ Ioc (0:ℝ) (0+1) ∩ Ioo δ (1-δ) := by
      intro x hx
      have hh := cut.ψ_support hx
      exact ⟨⟨by linarith [hh.1],by linarith [hh.2]⟩,hh⟩
    have hGden (i : PassageOutputIndex (S n)) : G.density i =
        exactRetainedPacketDensity (Ioo δ (1-δ)) (lawJitter ρ cut) (neutralCircleCutoff cut)
          (X i.1) (F.m i.1) H (F.A i.1) {i.2.val} n := by
      apply literal_packet_canonical_density G hGmod i (hGm i) (hGA i) ?_
        (continuous_quantileCircleJitter cut hρs hρi hρp hρm) hJs (fun _ _ => rfl)
        isOpen_Ioo (lawJitter_injOn cut hρs.continuous hρi hρp hρm hδ)
        (fun x hx => (hJd x hx).ne') (continuous_neutralCircleCutoff cut) cut.ψ_smooth cut.ψ_compact
        heψ hsψ (hXc i.1) (hXs i.1) hHc hHl hHe (F.continuous_amplitude i.1)
        (F.smooth_amplitude i.1) hn0
      intro a
      obtain ⟨x,rfl⟩ := Quotient.mk_surjective a
      change (G.V x:UnitAddCircle) = _
      rw [hGV]
      rfl
    refine ⟨G,?_,hGmod,hGV,hGm,hGA,hGden,?_,?_⟩
    · have he : G.m = fun i : PassageOutputIndex (S n) => i.2.val := funext hGm
      rw [he]
      exact output_index_injective (hSd n hn0)
    · intro i E inst
      simp_rw [hGden]
      exact exactRetainedPacketDensity_filtered_singletons hJs isOpen_Ioo (lawJitter_injOn cut hρs.continuous hρi hρp hρm hδ)
        (fun x hx => (hJd x hx).ne') cut.ψ_smooth cut.ψ_compact heψ hsψ (hXs i)
        hHl hHe (F.smooth_amplitude i) hn0 (hSN n hn0 i) E

    · obtain ⟨τG,hτG,hrG⟩ := literal_output_reflection F hr (neutralCircleCutoff cut) cut.ψ X H n (S n)
        (scalar_exact_indices_reflect hχsym (hTE' n hn0)) (fun i s _ => hχsym i s)
        G hGm hGA hGA₀
      refine ⟨τG,hτG,hrG,hGo,hGl,hGu,?_⟩
      intro x hx
      rw [hGV]
      exact positive_deriv_new_speed hn0 (hJd x hx)

end ThreeTorus
end
end

section

/-! Actual transmission with support-linked tracking and its smooth geometric
family. Its positive strength precedes every later finite literal packet list. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
universe u

theorem exists_signal_reflected_tracked_family
    {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ α : ℝ, ∃ L : ℕ, ∃ γ₀ : ℝ,
      0 < α ∧ α < b/2 ∧ 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (ι : Type u) [Fintype ι], ∀ (F : PassagePackets ι),
      Injective F.m → F.SpareIndependent → ∀ τref : ι → ι, F.Reflection τref → ∀ B : ℝ, 0 < B →
      (∀ i, b ≤ |(F.m i:ℝ)/B|) →
      ∀ ε η κ : ℝ, 0 < ε → 0 < η → 0 < κ →
      ∃ c : ℕ, 0 < c ∧ ∃ δ : ℝ, ∃ cut : LawCutoffs δ,
      ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      0 < δ ∧ δ < 1/8 ∧ δ < κ ∧
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, (c:ℝ)+F.V t)+Δ n*x):UnitAddCircle)) ∧
      let ρ := signalJitter α γ d (signalPrimeProduct L) B c
      let J := quantileCircleJitter ρ cut
      let J₀ := lawJitter ρ cut
      let σ := fun (n : ℕ) a => (((1+J a/n)/n:ℝ):UnitAddCircle)
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ Integrable ρ ∧
      (∀ y, 0 < ρ y) ∧ (∫ y, ρ y = 1) ∧
      (∀ n, Smooth (torusPassage (H n) (σ n)) ∧ Smooth (torusPassage (H n) (σ n)).symm ∧
        MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
      (∀ n, 0 < n → ∀ x : Cover,
        torusPassage (H n) (σ n) (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
        (torusPassage (H n) (σ n)).symm (project x) =
          project (passageFamily (fun t => (c:ℝ)+F.V t) J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
      (∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ e : ℕ,
        TendstoUniformlyOn
          (fun (n : ℕ) x => iteratedFDeriv ℝ e
            (passageFamily (fun t => (c:ℝ)+F.V t) J₀ r ((n:ℝ)⁻¹,Δ n)) x)
          (fun x => iteratedFDeriv ℝ e (fun y : Cover => ![y 0+r*((c:ℝ)+F.V (y 1)),y 1,y 2]) x)
          atTop K) ∧
      ∃ S : ℕ → ι → Finset ℤ, ∀ᶠ n : ℕ in atTop, 0 < n ∧
        ∃ G : PassagePackets (PassageOutputIndex (S n)),
          Injective G.m ∧ G.SpareIndependent ∧
          G.V = (fun x => (1+J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
          (∀ i,
            (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
              outputVector G i (passageChart (H n) x)‖^2 ∂tripleVolume) < ε ∧
            (∫ z, |outputDensity G i z-F.density i z*signalCircleModel
              (signalPrimeProduct L) γ B d (F.m i) ((n:ℤ) • z)| ∂phaseHaar) < ε) ∧
          (∀ i, ∃ x ∈ F.core i.1,
            |(G.m i:ℝ)/((n:ℝ)*c*B)-(F.m i.1:ℝ)/B| < η ∧
            ∀ y, dist ((G.m i:ℝ)*G.V y:UnitAddCircle)
              ((F.m i.1:ℝ)*F.V x:UnitAddCircle) < η) ∧
          ∃ τG : PassageOutputIndex (S n) → PassageOutputIndex (S n),
            (∀ i, (τG i).1 = τref i.1) ∧ G.Reflection τG ∧ G.GoodArc δ := by
  classical
  obtain ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,hfamily⟩ := exists_signal_state_reflected_family hb hbD hd hdc hdr hd0 hds
  refine ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,?_⟩
  intro γ hγp hγs
  obtain ⟨hdb,hstate⟩ := hfamily γ hγp hγs
  refine ⟨hdb,?_⟩
  intro ι inst F hi hmod τref hr B hB hm ε η κ hε hη hκ
  obtain ⟨P,_hP,hPV⟩ := F.speed_bound
  obtain ⟨M,_hM,hMm⟩ := F.angular_bound
  have hD i : |(F.m i:ℝ)/B| ≤ M/B := by
    rw [abs_div,abs_of_pos hB]
    exact div_le_div_of_nonneg_right (hMm i) hB.le
  let τ := η/4
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτη : τ < η/2 := by dsimp [τ]; linarith
  obtain ⟨c,hc,hbud⟩ := ((hstate ι F hi hmod τref hr B hB hm ε τ κ hε hτ hκ).and
    (support_drift_budgets (D := M/B) (P := P) (M := M) hB hη)).exists
  obtain ⟨hcp,δ,cut,χ,Δ,H,hδ,hδ',hδκ,hχ,_hχd,hΔ,hΔt,hHc,hHe,
    hρs,hρi,hρp,hρm,hgeo,hgraph,hlimit,S,_hSd,hS,hgood⟩ := hc
  have hb := hbud.2 τ hτ hτη
  obtain ⟨R,_hR,hRJ⟩ := periodic_real_bound (lawJitter_smooth cut hρs hρi hρp hρm).continuous
    (periodize_periodic _)
  refine ⟨c,hcp,δ,cut,Δ,H,hδ,hδ',hδκ,hΔ,hΔt,hHc,hHe,hρs,hρi,hρp,hρm,hgeo,hgraph,hlimit,S,?_⟩
  filter_upwards [hgood,hb.2 R] with n hn hnb
  obtain ⟨hnp,haul,G,hGi,hGmod,hGV,hGm,hGA,_hGden,hgroup,hreflect⟩ := hn
  refine ⟨hnp,G,hGi,hGmod,hGV,hGm,?_,?_,hreflect⟩
  · intro i
    have hv := outputVector_eq_retained F G (neutralCircleCutoff cut) (fun i s _ => χ i s)
      H n hGm hGA i
    have hp : exactRetainedPacketDensity (Ioo δ (1-δ))
        (lawJitter (signalJitter α γ d (signalPrimeProduct L) B c) cut)
        (neutralCircleCutoff cut) (fun s _ => χ i s) (F.m i) H (F.A i) (S n i) n =
        outputDensity G i := by
      have hh := hgroup i (fun _ => True)
      change _ = fun z => ∑ j : ↥(S n i), G.density ⟨i,j⟩ z
      simpa only [Finset.filter_true,ite_true] using hh
    have hh := haul i
    dsimp only at hh
    rw [← hv,hp] at hh
    exact ⟨hh.1,hh.2.1⟩
  · intro i
    obtain ⟨x,hx,ha,ht⟩ := literal_output_tracking hcp hnp hB hD hPV hMm hRJ
      (fun i j hj => (hS n hnp i j).mp hj) (fun i => (hχ i).2.2.2.2) hGm hGV i
    exact ⟨x,hx,ha.trans_lt hb.1,fun y => (ht y).trans_lt hnb.2⟩

end ThreeTorus
end
end

section

/-! Unconditional constructors of the tracked geometric state data. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
universe u

theorem exists_neutral_reflected_geometry_state {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) (hi : Injective F.m) (hmod : F.SpareIndependent)
    {τref : ι → ι} (hr : F.Reflection τref)
    {B D ε η κ : ℝ} (hB : 0 < B) (hD : ∀ i, |(F.m i:ℝ)/B| ≤ D)
    (hε : 0 < ε) (hη : 0 < η) (hκ : 0 < κ) {Q : ℕ} [NeZero Q] (hQ : 0 < Q) :
    ∃ g : PassageGeometryFamily F.V, ∃ S : ℕ → ι → Finset ℤ,
      ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ G : PassagePackets (PassageOutputIndex (S n)),
        Injective G.m ∧ G.SpareIndependent ∧
        G.V = (fun x => (1+g.J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
        (∀ i,
          (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
            outputVector G i (passageChart (g.H n) x)‖^2 ∂tripleVolume) < ε ∧
          (∫ z, |outputDensity G i z-F.density i z| ∂phaseHaar) < ε ∧
          (∑ h : Fin Q, ∫ z,
            |(∑ j : ↥(S n i), if signalResidue Q j.val = h then G.density ⟨i,j⟩ z else 0)-
              (Q:ℝ)⁻¹*F.density i z| ∂phaseHaar) < ε) ∧
        StateTracks F G Sigma.fst B (g.scale B n) η ∧
        ∃ τG : PassageOutputIndex (S n) → PassageOutputIndex (S n),
          (∀ i, (τG i).1 = τref i.1) ∧ G.Reflection τG ∧
          ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ G.GoodArc δ := by
  obtain ⟨c,hc,δ,cut,L,Δ,H,hδ,hδ',hδκ,_hL,hΔ,hΔt,hHc,hHe,hgeo,hgraph,hlimit,S,hgood⟩ :=
    exists_neutral_reflected_tracked_family F hi hmod hr hB hD hε hη hκ hQ
  let g : PassageGeometryFamily F.V :=
    ⟨c,hc,Δ,H,neutralJitter cut L 0,neutralJitterReal cut L 0,(fun _ => rfl),
      continuous_neutralJitter cut L 0,hΔ,hΔt,hHc,hHe,hgeo,hgraph,hlimit⟩
  refine ⟨g,S,?_⟩
  filter_upwards [hgood] with n hn
  obtain ⟨hnp,G,hGi,hGmod,hGV,hGm,herr,htrack,τG,hτG,hrG,hgoodG⟩ := hn
  exact ⟨hnp,G,hGi,hGmod,hGV,hGm,herr,htrack,τG,hτG,hrG,δ,hδ,hδ',hδκ,hgoodG⟩

theorem exists_signal_reflected_geometry_state
    {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ L : ℕ, ∃ γ₀ : ℝ, 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (ι : Type u) [Fintype ι], ∀ (F : PassagePackets ι),
      Injective F.m → F.SpareIndependent → ∀ τref : ι → ι, F.Reflection τref → ∀ B : ℝ, 0 < B →
      (∀ i, b ≤ |(F.m i:ℝ)/B|) →
      ∀ ε η κ : ℝ, 0 < ε → 0 < η → 0 < κ →
      ∃ g : PassageGeometryFamily F.V, ∃ S : ℕ → ι → Finset ℤ,
        ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ G : PassagePackets (PassageOutputIndex (S n)),
          Injective G.m ∧ G.SpareIndependent ∧
          G.V = (fun x => (1+g.J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
          (∀ i,
            (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
              outputVector G i (passageChart (g.H n) x)‖^2 ∂tripleVolume) < ε ∧
            (∫ z, |outputDensity G i z-F.density i z*signalCircleModel
              (signalPrimeProduct L) γ B d (F.m i) ((n:ℤ) • z)| ∂phaseHaar) < ε) ∧
          StateTracks F G Sigma.fst B (g.scale B n) η ∧
        ∃ τG : PassageOutputIndex (S n) → PassageOutputIndex (S n),
          (∀ i, (τG i).1 = τref i.1) ∧ G.Reflection τG ∧
          ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ G.GoodArc δ := by
  obtain ⟨α,L,γ₀,_hα,_hαb,hL,hLD,hγ₀,hfamily⟩ := exists_signal_reflected_tracked_family hb hbD hd hdc hdr hd0 hds
  refine ⟨L,γ₀,hL,hLD,hγ₀,?_⟩
  intro γ hγp hγs
  obtain ⟨hdb,hstate⟩ := hfamily γ hγp hγs
  refine ⟨hdb,?_⟩
  intro ι inst F hi hmod τref hr B hB hm ε η κ hε hη hκ
  obtain ⟨c,hc,δ,cut,Δ,H,hδ,hδ',hδκ,hΔ,hΔt,hHc,hHe,
    hρs,hρi,hρp,hρm,hgeo,hgraph,hlimit,S,hgood⟩ := hstate ι F hi hmod τref hr B hB hm ε η κ hε hη hκ
  let ρ := signalJitter α γ d (signalPrimeProduct L) B c
  let g : PassageGeometryFamily F.V :=
    ⟨c,hc,Δ,H,quantileCircleJitter ρ cut,lawJitter ρ cut,(fun _ => rfl),
      continuous_quantileCircleJitter cut hρs hρi hρp hρm,hΔ,hΔt,hHc,hHe,hgeo,hgraph,hlimit⟩
  refine ⟨g,S,?_⟩
  filter_upwards [hgood] with n hn
  obtain ⟨hnp,G,hGi,hGmod,hGV,hGm,herr,htrack,τG,hτG,hrG,hgoodG⟩ := hn
  exact ⟨hnp,G,hGi,hGmod,hGV,hGm,herr,htrack,τG,hτG,hrG,δ,hδ,hδ',hδκ,hgoodG⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
universe u

/-- Actual refresh/transmit state, with the exact positive strength fixed before
all data and error budgets. Each input packet can carry its original color's
continuous coefficient; finite color grouping is by summation. -/
theorem exists_refresh_transmit_reflected_state
    {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ L : ℕ, ∃ γ₀ : ℝ, 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (ι : Type u) [Fintype ι], ∀ (F : PassagePackets ι),
      Injective F.m → F.SpareIndependent → ∀ τref : ι → ι, F.Reflection τref → ∀ B : ℝ, 0 < B →
      ∀ margin : ℝ, 0 < margin →
      (∀ i, b+margin ≤ |(F.m i:ℝ)/B| ∧ |(F.m i:ℝ)/B| ≤ D-margin) →
      ∀ (a : ι → UnitAddCircle → ℂ), (∀ i, Continuous (a i)) →
      ∀ ω : ℝ, 0 ≤ ω →
      (∀ i x, x ∈ F.core i →
        ‖d ((F.m i:ℝ)/B)-a i ((F.m i:ℝ)*F.V x:UnitAddCircle)‖ ≤ ω) →
      ∀ ε η κ₀ : ℝ, 0 < ε → 0 < η → 0 < κ₀ →
      ∃ g : PassageGeometryFamily F.V, ∃ S : ℕ → ι → Finset ℤ,
        ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ G : PassagePackets (PassageOutputIndex (S n)),
          Injective G.m ∧ G.SpareIndependent ∧
          G.V = (fun x => (1+g.J₀ x/n)/n) ∧ (∀ i, G.m i = i.2.val) ∧
          ∃ g' : PassageGeometryFamily G.V,
          ∃ T : ℕ → PassageOutputIndex (S n) → Finset ℤ,
          ∀ᶠ N : ℕ in atTop, 0 < N ∧ ∃ K : PassagePackets (PassageOutputIndex (T N)),
            Injective K.m ∧ K.SpareIndependent ∧
            K.V = (fun x => (1+g'.J₀ x/N)/N) ∧ (∀ i, K.m i = i.2.val) ∧
            (∀ i,
              physicalError (packet (F.m i) (F.A i))
                (pairOutputVector K i ∘ passageChart (g'.H N) ∘ passageChart (g.H n)) < ε ∧
              (∫ z, |pairOutputDensity K i z-F.density i z*
                (1+2*refreshedStrength (signalPrimeProduct L) γ*
                  (fourier (-1) ((N:ℤ) • z)*a i z).re)| ∂phaseHaar) <
                2*γ*ω*(∫ z, |F.density i z| ∂phaseHaar)+ε) ∧
            StateTracks F K (Sigma.fst ∘ Sigma.fst) B (g'.scale (g.scale B n) N) η ∧
            ∃ τK : PassageOutputIndex (T N) → PassageOutputIndex (T N),
              (∀ i, ((τK i).1).1 = τref i.1.1) ∧ K.Reflection τK ∧
              ∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ₀ ∧ K.GoodArc δ := by
  classical
  obtain ⟨L,γ₀,hL,hLD,hγ₀,hfamily⟩ := exists_signal_reflected_geometry_state.{u} hb hbD hd hdc hdr hd0 hds
  refine ⟨L,γ₀,hL,hLD,hγ₀,?_⟩
  intro γ hγp hγs
  obtain ⟨hdb,hsignal⟩ := hfamily γ hγp hγs
  refine ⟨hdb,?_⟩
  intro ι inst F hi hmod τref hrF B hB margin hmargin hband a ha ω hω hmatch ε η κ₀ hε hη hκ₀
  obtain ⟨A,hA,haA⟩ := finite_circle_coefficients_bound a ha
  obtain ⟨M₀,hM₀⟩ := (Set.finite_range (fun i => ∫ z, |F.density i z| ∂phaseHaar)).isCompact.isBounded.exists_norm_le
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hmass i : (∫ z, |F.density i z| ∂phaseHaar) ≤ M :=
    (le_abs_self _).trans ((hM₀ _ (mem_range_self i)).trans (le_max_left _ _))
  obtain ⟨κ,r,t,hκ,hr,ht,hphys,hbud⟩ := refresh_pair_error_budgets hγp.le hω hA hM hε
  obtain ⟨η₀,hη₀,hcoeff⟩ := coefficient_match_drift_budget F hd.continuous hdc a ha hκ hmatch
  let η₁ := min η₀ (min margin (η/2))
  have hη₁ : 0 < η₁ := lt_min hη₀ (lt_min hmargin (half_pos hη))
  have hη₁₀ : η₁ ≤ η₀ := min_le_left _ _
  have hη₁m : η₁ ≤ margin := (min_le_right _ _).trans (min_le_left _ _)
  have hη₁η : η₁ ≤ η/2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨g,S,hrefresh⟩ := exists_neutral_reflected_geometry_state F hi hmod hrF hB
    (fun i => (hband i).2.trans (by linarith : D-margin ≤ D)) hr hη₁ hκ₀
    (signalPrimeProduct_pos L)
  refine ⟨g,S,?_⟩
  filter_upwards [hrefresh] with n hn
  obtain ⟨hnp,G,hGi,hGmod,hGV,hGm,hGerror,hGtrack,τG,hτG,hrG,_hgoodG⟩ := hn
  have hB' := g.scale_pos hB hnp
  have hGband j : b ≤ |(G.m j:ℝ)/g.scale B n| := by
    obtain ⟨x,_hx,ha',_ht'⟩ := hGtrack j
    exact (normalized_band_under_drift (hband j.1).1 (hband j.1).2
      (ha'.trans_le hη₁m)).1.le
  have hcm := hcoeff (PassageOutputIndex (S n)) G Sigma.fst (g.scale B n)
    ((hGtrack.mono hη₁₀).density)
  obtain ⟨e,he,heb⟩ := transmission_sum_budget (S n) ht
  obtain ⟨g',T,htransmit⟩ := hsignal (PassageOutputIndex (S n)) G hGi hGmod τG hrG
    (g.scale B n) hB' hGband e (η/2) κ₀ he (half_pos hη) hκ₀
  refine ⟨hnp,G,hGi,hGmod,hGV,hGm,g',T,?_⟩
  filter_upwards [htransmit] with N hN
  obtain ⟨hNp,K,hKi,hKmod,hKV,hKm,hKerror,hKtrack,τK,hτK,hrK,hgoodK⟩ := hN
  refine ⟨hNp,K,hKi,hKmod,hKV,hKm,?_,?_,τK,?_,hrK,hgoodK⟩
  · intro i
    constructor
    · have hsecond := transmission_pair_physical G K (g'.Hcontinuous N) i
        (fun j => (hKerror j).1) (heb i).2
      have hsecond' : physicalError (outputVector G i ∘ passageChart (g.H n))
          (pairOutputVector K i ∘ passageChart (g'.H N) ∘ passageChart (g.H n)) < t := by
        change physicalError (outputVector G i ∘ passageChart (g.H n))
          ((pairOutputVector K i ∘ passageChart (g'.H N)) ∘ passageChart (g.H n)) < t
        rwa [physicalError_chart (g.Hcontinuous n).measurable]
      have hfirst : physicalError (packet (F.m i) (F.A i))
          (outputVector G i ∘ passageChart (g.H n)) < r := (hGerror i).1
      have hh := physicalError_triangle (continuous_packet (m := F.m i) (F.continuous_amplitude i))
        ((continuous_outputVector G i).comp (continuous_passageChart (g.Hcontinuous n)))
        (((continuous_pairOutputVector K i).comp (continuous_passageChart (g'.Hcontinuous N))).comp
          (continuous_passageChart (g.Hcontinuous n)))
      change physicalError (packet (F.m i) (F.A i))
        (pairOutputVector K i ∘ passageChart (g'.H N) ∘ passageChart (g.H n)) ≤ _ at hh
      simp only [Function.comp_assoc] at hh
      linarith
    · let p : ↥(S n i) → UnitAddCircle → ℝ := fun j => G.density ⟨i,j⟩
      let rr : ↥(S n i) → Fin (signalPrimeProduct L) :=
        fun j => signalResidue (signalPrimeProduct L) (G.m ⟨i,j⟩)
      let cc : ↥(S n i) → ℂ := fun j => d ((G.m ⟨i,j⟩:ℝ)/g.scale B n)
      let ee : UnitAddCircle → ℂ := fun z => fourier (-1) ((N:ℤ) • z)
      have hee : Continuous ee := (fourier (-1)).continuous.comp (continuous_zsmul (N:ℤ))
      have hT := transmission_pair_density K
        (fun j z => G.density j z*signalCircleModel (signalPrimeProduct L) γ (g.scale B n) d (G.m j) ((N:ℤ) • z))
        (fun j => (G.density_continuous j).mul
          ((continuous_signalCircleModel _ _ _ _ _).comp (continuous_zsmul (N:ℤ)))) i
        (fun j => (hKerror j).2) (heb i).1
      have hmodel : (fun z => ∑ j : ↥(S n i), G.density ⟨i,j⟩ z*
        signalCircleModel (signalPrimeProduct L) γ (g.scale B n) d (G.m ⟨i,j⟩) ((N:ℤ) • z)) =
          refreshSignalAggregate rr (signalUnitResidues (signalPrimeProduct L)) p cc γ ee := by
        funext z
        exact signal_sum_aggregate _ _ _ _ _ _ _ _
      rw [show (∫ z, |pairOutputDensity K i z-(∑ j : ↥(S n i), G.density ⟨i,j⟩ z*
        signalCircleModel (signalPrimeProduct L) γ (g.scale B n) d (G.m ⟨i,j⟩) ((N:ℤ) • z))| ∂phaseHaar) =
        ∫ z, |pairOutputDensity K i z-refreshSignalAggregate rr
          (signalUnitResidues (signalPrimeProduct L)) p cc γ ee z| ∂phaseHaar by rw [← hmodel]] at hT
      have hE : (∫ z, refreshResidueError rr p (F.density i) z ∂phaseHaar) < r := by
        rw [refresh_residue_integral_eq G (F.density i) (F.density_continuous i) _ hGm i]
        exact (hGerror i).2.2
      have hbound := refresh_transmit_L1 rr (signalUnitResidues (signalPrimeProduct L)) cc
        (fun j => G.density_continuous ⟨i,j⟩) (ha i) hee (F.density_continuous i)
        (continuous_pairOutputDensity K i) hγp.le (by positivity : 0 ≤ ω+κ)
        (fun j z => G.density_nonneg ⟨i,j⟩ z)
        (fun z => by simpa only [ee,fourier_apply,Circle.norm_coe] using (le_refl (1:ℝ)))
        (haA i) (fun j z hj => hcm ⟨i,j⟩ z hj)
      simp only [Fintype.card_fin] at hbound
      change _ ≤ _ at hbound
      apply hbound.trans_lt
      exact hbud _ _ _ (integral_nonneg (fun _ => abs_nonneg _)) (hmass i)
        (integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))) hE hT
  · exact (hGtrack.trans hKtrack).mono (by linarith)
  · intro i
    rw [hτK,hτG]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

namespace ColoredState
variable {R : Type} [DecidableEq R] (C : ColoredState R)

def Reflection (τR : R → R) : Prop :=
  ∃ τ : C.Index → C.Index, C.packets.Reflection τ ∧
    ∀ i, C.color (τ i) = τR (C.color i)

lemma Reflection.density {τR : R → R} (hr : C.Reflection τR)
    (hτR : Involutive τR) (r : R) (z : UnitAddCircle) :
    C.density (τR r) z = C.density r (-z) := by
  classical
  obtain ⟨τ,hτ,hcolor⟩ := hr
  let e := (hτ.involutive C.injective).toPerm
  change (∑ i, if C.color i = τR r then C.packets.density i z else 0) =
    ∑ i, if C.color i = r then C.packets.density i (-z) else 0
  rw [← Equiv.sum_comp e (fun i => if C.color i = τR r then C.packets.density i z else 0)]
  apply Finset.sum_congr rfl
  intro i _
  change (if C.color (τ i) = τR r then C.packets.density (τ i) z else 0) = _
  rw [hcolor,hτ.density]
  simp only [hτR.injective.eq_iff]

end ColoredState

/-- Symmetric actual refresh--signal pairs, retaining the complete good arc
with arbitrarily small excluded measure. -/
theorem exists_colored_reflected_signal {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ L : ℕ, ∃ γ₀ : ℝ, 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (R : Type) [DecidableEq R], ∀ (C : ColoredState R),
      ∀ τR : R → R, C.Reflection τR →
      ∀ margin : ℝ, 0 < margin → C.InBand b D margin →
      ∀ (a : R → UnitAddCircle → ℂ), (∀ r, Continuous (a r)) →
      ∀ ω : ℝ, 0 ≤ ω → C.Matches d a ω →
      ∀ ε η κ : ℝ, 0 < ε → 0 < η → 0 < κ →
      ∀ᶠ N : ℕ in atTop, ∃ s : ColoredPair C N, s.Tracks η ∧
        s.output.Reflection τR ∧
        (∃ δ : ℝ, 0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ s.final.GoodArc δ) ∧
        ∀ r,
        physicalError (C.vector r) (s.output.vector r ∘ s.chart) < ε ∧
        (∫ z, |s.output.density r z-C.density r z*
          colorFactor a (refreshedStrength (signalPrimeProduct L) γ) (N:ℤ) r z| ∂phaseHaar) <
            2*γ*ω*(∫ z, C.density r z ∂phaseHaar)+ε := by
  classical
  obtain ⟨L,γ₀,hL,hLD,hγ₀,hfamily⟩ := exists_refresh_transmit_reflected_state hb hbD hd hdc hdr hd0 hds
  refine ⟨L,γ₀,hL,hLD,hγ₀,?_⟩
  intro γ hγ hγs
  obtain ⟨hsmall,hpair⟩ := hfamily γ hγ hγs
  refine ⟨hsmall,?_⟩
  intro R inst C τR hrC margin hmargin hband a ha ω hω hmatch ε η κ hε hη hκ
  obtain ⟨τ,hr,hτ⟩ := hrC
  obtain ⟨e,he,hecard,hecard2⟩ := finite_card_error_budget C.Index hε
  obtain ⟨g,S,hG⟩ := hpair C.Index C.packets C.injective C.spare τ hr C.scale C.scale_pos
    margin hmargin hband (fun i => a (C.color i)) (fun i => ha (C.color i))
    ω hω hmatch e η κ he hη hκ
  obtain ⟨n,hn⟩ := hG.exists
  obtain ⟨hnp,G,hGi,hGmod,hGV,hGm,g',T,hK⟩ := hn
  filter_upwards [hK] with N hN
  obtain ⟨hNp,K,hKi,hKmod,hKV,hKm,herror,htrack,τK,hτK,hrK,hgoodK⟩ := hN
  let s : ColoredPair C N :=
    ⟨g,S n,n,hnp,G,hGi,hGmod,hGV,hGm,g',T N,hNp,K,hKi,hKmod,hKV,hKm⟩
  refine ⟨s,htrack,⟨τK,hrK,?_⟩,hgoodK,?_⟩
  · intro i
    change C.color ((τK i).1.1) = τR (C.color i.1.1)
    exact (congrArg C.color (hτK i)).trans (hτ i.1.1)
  · exact color_pair_errors C.packets K C.color a ha (g.Hcontinuous n) (g'.Hcontinuous N)
      N (refreshedStrength (signalPrimeProduct L) γ) he hecard hecard2 herror

end ThreeTorus
end
end

section

/-! Finite physical C-infinity restrictions, on both the map and inverse,
threaded through the actual refresh and transmission integer choices. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

structure PhysicalJetData where
  size : ℕ
  sign : Fin size → ℤ
  domain : Fin size → Set Cover
  compact : ∀ i, IsCompact (domain i)
  order : Fin size → ℕ

namespace PhysicalJetData

def Close (Q : PhysicalJetData) (ε : ℝ) (F : PhysicalFrame) (V : ℝ → ℝ)
    (G : PhysicalFrame) (W : ℝ → ℝ) : Prop :=
  ∀ i x, x ∈ Q.domain i → dist
    (iteratedFDeriv ℝ (Q.order i) (G.mapLift W (Q.sign i)) x)
    (iteratedFDeriv ℝ (Q.order i) (F.mapLift V (Q.sign i)) x) ≤ ε

lemma close_refl (Q : PhysicalJetData) (F : PhysicalFrame) (V : ℝ → ℝ) :
    Q.Close 0 F V F V := by intro i x hx; simp

lemma Close.mono {Q : PhysicalJetData} {ε η : ℝ} {F G : PhysicalFrame} {V W : ℝ → ℝ}
    (h : Q.Close ε F V G W) (he : ε ≤ η) : Q.Close η F V G W :=
  fun i x hx => (h i x hx).trans he

lemma Close.trans {Q : PhysicalJetData} {ε η : ℝ} {F G H : PhysicalFrame}
    {V W U : ℝ → ℝ} (h : Q.Close ε F V G W) (h' : Q.Close η G W H U) :
    Q.Close (ε+η) F V H U := by
  intro i x hx
  exact (dist_triangle _ _ _).trans (by linarith [h i x hx,h' i x hx])

lemma eventually_next (Q : PhysicalJetData) (F : PhysicalFrame) {V : ℝ → ℝ}
    (g : PassageGeometryFamily V) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g.J₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Q.Close ε F V (F.next g hV n) (fun a => (1+g.J₀ a/n)/n) := by
  have hj : ∀ᶠ n : ℕ in atTop, ∀ i : Fin Q.size, ∀ x ∈ Q.domain i,
      dist (iteratedFDeriv ℝ (Q.order i)
        (fun y => F.backward (Q.sign i) (g.correctedFamily (Q.sign i:ℝ)
          ((n:ℝ)⁻¹,g.Δ n) (F.forward y))) x)
        (iteratedFDeriv ℝ (Q.order i) (F.mapLift V (Q.sign i)) x) < ε := by
    apply eventually_all.2
    intro i
    simpa only [PhysicalFrame.mapLift,coverTwist,Function.comp_def,dist_comm] using
      (Metric.tendstoUniformlyOn_iff.1 (g.physical_jets_tendsto hV hJ F.forward_smooth
        (F.backward_smooth (Q.sign i)) (Q.sign i:ℝ) (Q.compact i) (Q.order i))) ε hε
  filter_upwards [hj,eventually_gt_atTop 0] with n hn hnp
  intro i x hx
  rw [F.next_mapLift g hV hnp]
  exact (hn i x hx).le

end PhysicalJetData

namespace ColoredPair
variable {R : Type} {C : ColoredState R} {N : ℕ} (s : ColoredPair C N)

def nextFrame (F : PhysicalFrame) : PhysicalFrame :=
  (F.next s.refresh C.packets.smooth_speed s.n).next s.transmit s.middle.smooth_speed N

lemma nextFrame_chart (F : PhysicalFrame) : (s.nextFrame F).chart = F.chart.trans s.chart := by
  apply Equiv.ext
  intro x
  rfl

end ColoredPair

end ThreeTorus
end
end

section

/-! Unconditional neutral passage for general spare-dependent amplitudes and
possibly repeated old modes. Cutoffs and old families are fixed before all
jitter and passage-integer selections. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- Generic actual neutral output. It intentionally does not assert
injectivity of the new modes: the first support separation does not give it. -/
theorem exists_general_neutral {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) {c : ℕ} (hc : 0 < c)
    (h0 : ∀ x : ℝ, (c:ℝ)+F.V x ≠ 0)
    (χ : ι → ℝ → UnitAddCircle → ℝ)
    (hχs : ∀ i, CylinderSmooth (χ i).uncurry)
    (hχc : ∀ i, HasCompactSupport (χ i).uncurry)
    (hχ0 : ∀ i a, χ i 0 a = 0)
    (hχb : ∀ i s a, 0 ≤ χ i s a ∧ χ i s a ≤ 1)
    (hχW : ∀ i (C : Set ℝ) a s, stationaryWeight C
      (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i a) s ≠ 0 → χ i s a = 1)
    {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ L : ℝ, ∃ g : PassageGeometryFamily F.V,
      0 < δ ∧ δ < 1/8 ∧ δ < κ ∧ 0 < L ∧ g.c = c ∧
      g.J = neutralJitter cut L 0 ∧ g.J₀ = neutralJitterReal cut L 0 ∧
      ∃ S : ℕ → ι → Finset ℤ,
        (∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0) ∧
        ∀ᶠ n : ℕ in atTop, 0 < n ∧
          ∃ G : PassagePackets (PassageOutputIndex (S n)),
            G.SpareIndependent ∧ G.V = (fun x => (1+g.J₀ x/n)/n) ∧
            (∀ i, G.m i = i.2.val) ∧
            (∀ i, G.A i = retainedAmplitude (neutralCircleCutoff cut) (χ i.1)
              (F.m i.1) g.H (F.A i.1) n i.2.val) ∧
            (∀ i, G.A₀ i = retainedRealAmplitude cut.ψ (χ i.1) (F.m i.1) (g.H n)
              (F.A i.1) ((i.2.val:ℝ)/n) i.2.val) ∧
            G.GoodArc δ ∧
            ∀ i, (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
              outputVector G i (passageChart (g.H n) x)‖^2 ∂tripleVolume) < ε ∧
              (∫ z, |outputDensity G i z-F.marginalDensity i z| ∂phaseHaar) < ε := by
  classical
  obtain ⟨B,hB,hAB⟩ := F.amplitude_bound
  have hden : 0 < 32*(B+1) := by positivity
  obtain ⟨δ,hδ,hδall⟩ := exists_between (lt_min
    (lt_min (by norm_num : (0:ℝ)<1/8) (div_pos hε hden)) hκ)
  have hδhi := hδall.trans_le (min_le_left _ _)
  have hδκ := hδall.trans_le (min_le_right _ _)
  have hδ' : δ < 1/8 := hδhi.trans_le (min_le_left _ _)
  have hδB : 8*δ*B < ε/4 := by
    have hh := (lt_div_iff₀ hden).mp (hδhi.trans_le (min_le_right _ _))
    nlinarith
  let cut := lawCutoffs δ hδ hδ'
  let Fc := F.carrier (c:ℤ)
  have hXc i : Continuous (χ i).uncurry := (hχs i).continuous
  have hXW i s a : stationaryWeight (Icc (Fc.l-Fc.R) (Fc.u+Fc.R))
      (fun x => (Fc.m i:ℝ)*Fc.V x) (Fc.A₀ i a) s ≠ 0 → χ i s a = 1 := by
    simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using
      hχW i (Icc (F.l-F.R) (F.u+F.R)) a s
  have hzero i : 0 ∉ (fun x => (Fc.m i:ℝ)*Fc.V x) '' Icc Fc.l Fc.u := by
    rintro ⟨x,_hx,he⟩
    have hh : (F.m i:ℝ)*((c:ℝ)+F.V x) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast F.nonzero i) (h0 x)
    exact hh (by simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using he)
  obtain ⟨Δ,H,hΔ,hΔt,hHc,hHe,C,_hC,hrest⟩ :=
    exists_simultaneous_neutral_passage Fc.nonzero Fc.lift_matches Fc.two Fc.continuous_lift
      Fc.continuous_deriv Fc.smooth_lift Fc.support_lift Fc.lo Fc.uo Fc.lu Fc.Rpos
      Fc.periodic Fc.smooth_speed Fc.positive_deriv hzero Fc.continuous_amplitude Fc.smooth_amplitude
      (B := fun _ => B) (fun _ => hB) hAB cut hδ hδ' hχs hXc hχc hχ0 hχb hXW
  have hsmall : 0 < ε/4 := by positivity
  have hCT i : ∀ᶠ L : ℝ in atTop, C i/L < ε/4 :=
    (tendsto_const_nhds.div_atTop tendsto_id).eventually (gt_mem_nhds hsmall)
  obtain ⟨L,hL,hCL⟩ := ((eventually_gt_atTop (0:ℝ)).and ((Filter.eventually_all).mpr hCT)).exists
  obtain ⟨hgeo,hgraph,hlimit,S,hSN,_hST,hTE,hgood⟩ := hrest L hL 0
  let g : PassageGeometryFamily F.V := {
    c := c, c_pos := hc, Δ := Δ, H := H,
    J := neutralJitter cut L 0, J₀ := neutralJitterReal cut L 0,
    Jmatch := fun _ => rfl, Jcontinuous := continuous_neutralJitter cut L 0,
    delta_bound := hΔ, delta_tendsto := hΔt, Hcontinuous := hHc,
    Hformula := by simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using hHe,
    geometry := hgeo,
    graph := by simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using hgraph,
    convergence := by simpa only [Fc,PassagePackets.carrier,Int.cast_natCast] using hlimit }
  refine ⟨δ,cut,L,g,hδ,hδ',hδκ,hL,rfl,rfl,rfl,S,hTE,?_⟩
  filter_upwards [hgood (ε/4) hsmall] with n hn
  have hn0 := hn.1
  let Hl (n : ℕ) (x : ℝ) := (n:ℝ)*((∫ t in 0..x, Fc.V t)+Δ n*x)
  have hHl n : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n) :=
    contDiff_const.mul ((contDiff_real_primitive Fc.smooth_speed).add (contDiff_const.mul contDiff_id))
  have hJs := neutralJitterReal_smooth cut L 0
  have hJd x (hx : x ∈ Ioo δ (1-δ)) : 0 < deriv (neutralJitterReal cut L 0) x := by
    rw [neutralJitterReal_deriv cut hδ L 0 hx]
    exact hL
  obtain ⟨G,hGm,hGA,hGA₀,hGV,hGo,hGl,hGu,hGmod⟩ := literal_output_packets
    F.m F.A H Hl χ (S n) (hSN n hn0) F.continuous_amplitude F.smooth_amplitude
    hχs hXc hHc hHl hHe cut hδ hδ' (neutralJitterReal_periodic cut L 0) hJs hJd hn0
  have heψ : ∀ x ∈ Ioc (0:ℝ) (0+1), neutralCircleCutoff cut (x:UnitAddCircle) = cut.ψ x := by
    intro x hx
    rw [neutralCircleCutoff_coe]
    exact periodize_eq_on_unit ((subset_tsupport cut.ψ).trans
      (cut.ψ_support.trans (by intro z hz; constructor <;> linarith [hz.1,hz.2]))) ⟨hx.1.le,by simpa using hx.2⟩
  have hsψ : tsupport cut.ψ ⊆ Ioc (0:ℝ) (0+1) ∩ Ioo δ (1-δ) := by
    intro x hx
    have hh := cut.ψ_support hx
    exact ⟨⟨by linarith [hh.1],by linarith [hh.2]⟩,hh⟩
  have hJinj : InjOn (neutralJitterReal cut L 0) (Ioo δ (1-δ)) := by
    intro x hx y hy he
    rw [neutralJitterReal_affine cut hδ L 0 ⟨hx.1.le,hx.2.le⟩,
      neutralJitterReal_affine cut hδ L 0 ⟨hy.1.le,hy.2.le⟩] at he
    nlinarith
  have hGden (i : PassageOutputIndex (S n)) : G.density i =
      exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal cut L 0) (neutralCircleCutoff cut)
        (χ i.1) (F.m i.1) H (F.A i.1) {i.2.val} n := by
    apply literal_packet_canonical_density G hGmod i (hGm i) (hGA i) ?_
      (continuous_neutralJitter cut L 0) hJs (fun _ _ => rfl) isOpen_Ioo hJinj
      (fun x hx => (hJd x hx).ne') (continuous_neutralCircleCutoff cut) cut.ψ_smooth cut.ψ_compact
      heψ hsψ (hXc i.1) (hχs i.1) hHc hHl hHe (F.continuous_amplitude i.1)
      (F.smooth_amplitude i.1) hn0
    intro a
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective a
    change (G.V x:UnitAddCircle) = _
    rw [hGV]
    rfl
  have hgroup i : exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal cut L 0)
      (neutralCircleCutoff cut) (χ i) (F.m i) H (F.A i) (S n i) n = outputDensity G i := by
    have hh := exactRetainedPacketDensity_filtered_singletons (m := F.m i) hJs isOpen_Ioo hJinj
      (fun x hx => (hJd x hx).ne') cut.ψ_smooth cut.ψ_compact heψ hsψ (hχs i)
      hHl hHe (F.smooth_amplitude i) hn0 (hSN n hn0 i) (fun _ => True)
    simp only [Finset.filter_true,ite_true] at hh
    rw [hh]
    unfold outputDensity
    simp_rw [hGden]
  refine ⟨hn0,G,hGmod,hGV,hGm,hGA,hGA₀,⟨hGo,hGl,hGu,?_⟩,?_⟩
  · intro x hx
    rw [hGV]
    exact positive_deriv_new_speed hn0 (hJd x hx)
  · intro i
    have hh := hn.2 i
    dsimp only at hh
    rw [show Fc.m = F.m from rfl,show Fc.A = F.A from rfl] at hh
    have hv := outputVector_eq_retained F G (neutralCircleCutoff cut) χ H n hGm hGA i
    have hde : (∫ z, |outputDensity G i z-Fc.marginalDensity i z| ∂phaseHaar) =
        ∫ z, |outputDensity G i z-F.marginalDensity i z| ∂phaseHaar := by
      apply integral_congr_ae
      filter_upwards [F.marginalDensity_carrier (c:ℤ) i] with z hz
      rw [hz]
    change _ ∧ (∫ z, |outputDensity G i z-F.marginalDensity i z| ∂phaseHaar) < ε
    rw [← hv] at hh
    refine ⟨hh.1.trans (by linarith),?_⟩
    have hds : (∫ z, |outputDensity G i z-Fc.marginalDensity i z| ∂phaseHaar) < C i/L+4*δ*B+ε/4 := by
      change (∫ z, |outputDensity G i z-foldCircleDensity (fun s => ∫ a,
        stationaryWeight (Icc (Fc.l-Fc.R) (Fc.u+Fc.R)) (fun x => (Fc.m i:ℝ)*Fc.V x)
          (Fc.A₀ i a) s ∂AddCircle.haarAddCircle) z| ∂phaseHaar) < _
      rw [← hgroup]
      exact hh.2.1
    rw [hde] at hds
    exact hds.trans (by linarith [hCL i])

end ThreeTorus
end
end

section

/-! Actual general neutral steps with arbitrary repeated indices, carrying the
literal coefficient formulas, physical charts and controlled cover jets. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

structure NeutralStep {ι : Type*} (F : PassagePackets ι) where
  δ : ℝ
  cut : LawCutoffs δ
  L : ℝ
  δpos : 0 < δ
  δsmall : δ < 1/8
  Lpos : 0 < L
  geometry : PassageGeometryFamily F.V
  jitter : geometry.J₀ = neutralJitterReal cut L 0
  n : ℕ
  positive : 0 < n
  χ : ι → ℝ → UnitAddCircle → ℝ
  S : ι → Finset ℤ
  indices : ∀ i j, j ∈ S i ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0
  final : PassagePackets (PassageOutputIndex S)
  spare : final.SpareIndependent
  speed : final.V = (fun x => (1+geometry.J₀ x/n)/n)
  mode : ∀ i, final.m i = i.2.val
  amplitude : ∀ i, final.A i = retainedAmplitude (neutralCircleCutoff cut) (χ i.1)
    (F.m i.1) geometry.H (F.A i.1) n i.2.val
  lift : ∀ i, final.A₀ i = retainedRealAmplitude cut.ψ (χ i.1) (F.m i.1) (geometry.H n)
    (F.A i.1) ((i.2.val:ℝ)/n) i.2.val
  good : final.GoodArc δ

namespace NeutralStep
variable {ι : Type*} {F : PassagePackets ι} (s : NeutralStep F)

def chart : Equiv.Perm TripleTorus := passageChart (s.geometry.H s.n)
def nextFrame (frame : PhysicalFrame) : PhysicalFrame :=
  frame.next s.geometry F.smooth_speed s.n

lemma nextFrame_chart (frame : PhysicalFrame) :
    (s.nextFrame frame).chart = frame.chart.trans s.chart := rfl

lemma nonzero (i : ι) (j : ℤ) (hj : j ∈ s.S i) : j ≠ 0 := by
  simpa only [s.mode] using s.final.nonzero ⟨i,⟨j,hj⟩⟩

lemma reflection {τ : ι → ι} (hr : F.Reflection τ) (hτ : Involutive τ)
    (hχ : ∀ i x a, s.χ (τ i) x a = s.χ i (-x) a) :
    ∃ τG : PassageOutputIndex s.S → PassageOutputIndex s.S,
      (∀ i, (τG i).1 = τ i.1) ∧ Involutive τG ∧ s.final.Reflection τG := by
  have hs (i : ι) (j : ℤ) : j ∈ s.S (τ i) ↔ -j ∈ s.S i := by
    rw [s.indices,s.indices]
    simp only [hχ,Int.cast_neg,neg_div]
  obtain ⟨τG,hparent,hrG⟩ := literal_output_reflection F hr (neutralCircleCutoff s.cut)
    s.cut.ψ s.χ s.geometry.H s.n s.S hs hχ s.final s.mode s.amplitude s.lift
  refine ⟨τG,hparent,?_,hrG⟩
  intro i
  have h₁ : (τG (τG i)).1 = i.1 := by rw [hparent,hparent,hτ]
  have h₂ : (τG (τG i)).2.val = i.2.val := by
    rw [← s.mode,hrG.index,hrG.index,neg_neg,s.mode]
  have hext (a b : PassageOutputIndex s.S) (hp : a.1 = b.1) (hm : a.2.val = b.2.val) : a = b := by
    rcases a with ⟨a,ja⟩
    rcases b with ⟨b,jb⟩
    dsimp only at hp hm
    subst b
    exact congrArg (Sigma.mk a) (Subtype.ext hm)
  exact hext _ _ h₁ h₂

end NeutralStep

/-- Finite physical restrictions are imposed only after the coefficients,
cutoffs, carrier, broad jitter and its rounding sequence have all been fixed. -/
theorem exists_controlled_neutral {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) {c : ℕ} (hc : 0 < c)
    (h0 : ∀ x : ℝ, (c:ℝ)+F.V x ≠ 0)
    (χ : ι → ℝ → UnitAddCircle → ℝ)
    (hχs : ∀ i, CylinderSmooth (χ i).uncurry)
    (hχc : ∀ i, HasCompactSupport (χ i).uncurry)
    (hχ0 : ∀ i a, χ i 0 a = 0)
    (hχb : ∀ i x a, 0 ≤ χ i x a ∧ χ i x a ≤ 1)
    (hχW : ∀ i (C : Set ℝ) a x, stationaryWeight C
      (fun t => (F.m i:ℝ)*((c:ℝ)+F.V t)) (F.A₀ i a) x ≠ 0 → χ i x a = 1)
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ s : NeutralStep F, s.χ = χ ∧ s.geometry.c = c ∧ s.δ < κ ∧
      Q.Close ζ frame F.V (s.nextFrame frame) s.final.V ∧
      ∀ i, (∫ x : TripleTorus, ‖packet (F.m i) (F.A i) x-
        outputVector s.final i (s.chart x)‖^2 ∂tripleVolume) < ε ∧
        (∫ z, |outputDensity s.final i z-F.marginalDensity i z| ∂phaseHaar) < ε := by
  classical
  obtain ⟨δ,cut,L,g,hδ,hδ',hδκ,hL,hgc,_hgJ,hgJ₀,S,hS,hgood⟩ :=
    exists_general_neutral F hc h0 χ hχs hχc hχ0 hχb hχW hε hκ
  have hJs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g.J₀ := by
    rw [hgJ₀]
    exact neutralJitterReal_smooth cut L 0
  obtain ⟨n,hn,hjet⟩ := (hgood.and (Q.eventually_next frame g F.smooth_speed hJs hζ)).exists
  obtain ⟨hnp,G,hGmod,hGV,hGm,hGA,hGA₀,hGgood,herr⟩ := hn
  let s : NeutralStep F := ⟨δ,cut,L,hδ,hδ',hL,g,hgJ₀,n,hnp,χ,S n,hS n hnp,
    G,hGmod,hGV,hGm,hGA,hGA₀,hGgood⟩
  refine ⟨s,rfl,hgc,hδκ,?_,herr⟩
  change Q.Close ζ frame F.V (frame.next g F.smooth_speed n) G.V
  rw [hGV]
  exact hjet

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- An arbitrary cofinal restriction may be imposed on the LAST integer. No
passage or smooth producer is assumed by this restriction. -/
theorem exists_controlled_neutral_eventually {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) {c : ℕ} (hc : 0 < c)
    (h0 : ∀ x : ℝ, (c:ℝ)+F.V x ≠ 0)
    (χ : ι → ℝ → UnitAddCircle → ℝ)
    (hχs : ∀ i, CylinderSmooth (χ i).uncurry)
    (hχc : ∀ i, HasCompactSupport (χ i).uncurry)
    (hχ0 : ∀ i a, χ i 0 a = 0)
    (hχb : ∀ i x a, 0 ≤ χ i x a ∧ χ i x a ≤ 1)
    (hχW : ∀ i (C : Set ℝ) a x, stationaryWeight C
      (fun t => (F.m i:ℝ)*((c:ℝ)+F.V t)) (F.A₀ i a) x ≠ 0 → χ i x a = 1)
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    (P : ℕ → Prop) (hP : ∀ᶠ n : ℕ in atTop, P n)
    {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ s : NeutralStep F, s.χ = χ ∧ s.geometry.c = c ∧ s.δ < κ ∧ P s.n ∧
      Q.Close ζ frame F.V (s.nextFrame frame) s.final.V ∧
      ∀ i, physicalError (packet (F.m i) (F.A i))
        (outputVector s.final i ∘ s.chart) < ε ∧
        (∫ z, |outputDensity s.final i z-F.marginalDensity i z| ∂phaseHaar) < ε := by
  classical
  obtain ⟨δ,cut,L,g,hδ,hδ',hδκ,hL,hgc,_hgJ,hgJ₀,S,hS,hgood⟩ :=
    exists_general_neutral F hc h0 χ hχs hχc hχ0 hχb hχW hε hκ
  have hJs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g.J₀ := by
    rw [hgJ₀]
    exact neutralJitterReal_smooth cut L 0
  obtain ⟨n,⟨hn,hjet⟩,hPn⟩ :=
    ((hgood.and (Q.eventually_next frame g F.smooth_speed hJs hζ)).and hP).exists
  obtain ⟨hnp,G,hGmod,hGV,hGm,hGA,hGA₀,hGgood,herr⟩ := hn
  let s : NeutralStep F := ⟨δ,cut,L,hδ,hδ',hL,g,hgJ₀,n,hnp,χ,S n,hS n hnp,
    G,hGmod,hGV,hGm,hGA,hGA₀,hGgood⟩
  refine ⟨s,rfl,hgc,hδκ,hPn,?_,herr⟩
  change Q.Close ζ frame F.V (frame.next g F.smooth_speed n) G.V
  rw [hGV]
  exact hjet

lemma compact_cylinder_gap {ι : Type*} [Finite ι]
    (χ : ι → ℝ → UnitAddCircle → ℝ)
    (hc : ∀ i, HasCompactSupport (χ i).uncurry)
    (h0 : ∀ i, tsupport (χ i).uncurry ⊆ {p | p.1 ≠ 0}) :
    ∃ a : ℝ, 0 < a ∧ ∀ i x z, χ i x z ≠ 0 → a ≤ |x| := by
  let E : Set ℝ := ⋃ i, Prod.fst '' tsupport (χ i).uncurry
  have hE : IsCompact E := isCompact_iUnion (fun i => (hc i).image continuous_fst)
  have hz : 0 ∉ E := by
    rintro ⟨_,⟨i,rfl⟩,p,hp,he⟩
    exact h0 i hp he
  obtain ⟨a,ha,haE⟩ := Metric.mem_nhds_iff.1 (hE.isClosed.isOpen_compl.mem_nhds hz)
  refine ⟨a,ha,?_⟩
  intro i x z hx
  by_contra h
  have hxE : x ∈ E := mem_iUnion.2 ⟨i,⟨(x,z),subset_tsupport _ hx,rfl⟩⟩
  exact haE (by simpa [Metric.mem_ball,Real.dist_eq] using lt_of_not_ge h) hxE

lemma eventually_retained_indices_large {ι : Type*}
    (χ : ι → ℝ → UnitAddCircle → ℝ) {a : ℝ} (ha : 0 < a)
    (hχ : ∀ i x z, χ i x z ≠ 0 → a ≤ |x|) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ i (j : ℤ), (∃ z, χ i ((j:ℝ)/n) z ≠ 0) → K < |(j:ℝ)| := by
  have hn : ∀ᶠ n : ℕ in atTop, K/a < (n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  filter_upwards [hn,eventually_gt_atTop 0] with n hn hnp
  intro i j hj
  obtain ⟨z,hz⟩ := hj
  have hr : (0:ℝ) < n := by exact_mod_cast hnp
  have hh := hχ i _ z hz
  rw [abs_div,abs_of_pos hr] at hh
  have hk : K < a*(n:ℝ) := (div_lt_iff₀ ha).mp hn |>.trans_eq (mul_comm _ _)
  exact hk.trans_le ((le_div_iff₀ hr).mp hh)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- The simultaneous-list version of neutral cutoffs: repeated occurrences of
one angular mode share exactly the same cutoff, whereas different modes have
disjoint retained sets. In particular F and H are not falsely declared
orthogonal to one another. -/
theorem mode_grouped_neutral_cutoffs {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) (τ : ι → ι) (_hτ : Involutive τ) (hr : F.Reflection τ) :
    ∃ c : ℕ, 0 < c ∧ (∀ x : ℝ, (c:ℝ)+F.V x ≠ 0) ∧
      ∃ χ : ι → ℝ → UnitAddCircle → ℝ,
        (∀ i, CylinderSmooth (χ i).uncurry ∧ HasCompactSupport (χ i).uncurry ∧
          tsupport (χ i).uncurry ⊆ {p | p.1 ≠ 0} ∧
          (∀ s a, 0 ≤ χ i s a ∧ χ i s a ≤ 1) ∧
          ∀ (C : Set ℝ) a s, stationaryWeight C
            (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i a) s ≠ 0 → χ i s a = 1) ∧
        (∀ i j, F.m i ≠ F.m j → Disjoint (tsupport (χ i).uncurry) (tsupport (χ j).uncurry)) ∧
        (∀ i j, F.m i = F.m j → χ i = χ j) ∧
        (∀ i s a, χ (τ i) s a = χ i (-s) a) := by
  classical
  let m : Option ι → ℤ := fun i => i.elim 1 F.m
  have hm (i : Option ι) : m i ≠ 0 := by
    cases i with
    | none => norm_num [m]
    | some i => exact F.nonzero i
  obtain ⟨c,hc,hc0,hsep⟩ := exists_integral_speed_separation m F.periodic.lift hm F.speed_continuous
  let V : ℝ → ℝ := fun x => (c:ℝ)+F.V x
  have h0 (x : ℝ) : V x ≠ 0 := by simpa [m,V] using hc0 none (x:UnitAddCircle)
  have hV : Continuous V := continuous_const.add F.smooth_speed.continuous
  let M := ↥(range F.m)
  let : Finite M := (finite_range F.m).to_subtype
  let a (i : ι) : M := ⟨F.m i,mem_range_self i⟩
  let negM (k : M) : M := ⟨-k.val,by
    obtain ⟨i,hi⟩ := k.property
    exact ⟨τ i,by simp only [hr.index,hi]⟩⟩
  have hneg (i : ι) : a (τ i) = negM (a i) := Subtype.ext (hr.index i)
  have hnn (k : M) : negM (negM k) = k := Subtype.ext (neg_neg _)
  let E (k : M) : Set (ℝ × UnitAddCircle) :=
    ⋃ i : {i : ι // F.m i = k.val}, stationaryImage (F.m i.val) V (F.cylinderCore i.val)
  have hEc k : IsCompact (E k) := isCompact_iUnion (fun i =>
    stationaryImage_compact hV (F.cylinderCore_compact i.val))
  have hEd : Pairwise (Disjoint on E) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro p hp hq
    obtain ⟨i,pi,hpi,hip⟩ := mem_iUnion.mp hp
    obtain ⟨j,pj,hpj,hjp⟩ := mem_iUnion.mp hq
    have hh := congrArg Prod.fst (hip.trans hjp.symm)
    have hij := hsep (some i.val) (some j.val) (pi.1:UnitAddCircle) (pj.1:UnitAddCircle) hh
    exact hkl (Subtype.ext (i.property.symm.trans (hij.trans j.property)))
  let U : Set (ℝ × UnitAddCircle) := {p | p.1 ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun continuous_fst continuous_const
  have hEU k : E k ⊆ U := by
    intro p hp
    obtain ⟨i,q,hq,rfl⟩ := mem_iUnion.mp hp
    exact mul_ne_zero (by exact_mod_cast F.nonzero i.val) (h0 q.1)
  obtain ⟨ξ,hξ,hξd⟩ := finite_disjoint_cylinder_cutoffs E (fun _ => U) hEc (fun _ => hU) hEU hEd
  let χ : ι → ℝ → UnitAddCircle → ℝ := fun i s z => ξ (a i) (s,z)*ξ (negM (a i)) (-s,z)
  have hsub i : tsupport (χ i).uncurry ⊆ tsupport (ξ (a i)) := tsupport_mul_subset_left
  have hre i {s : ℝ} {z : UnitAddCircle} (hs : (s,z) ∈ stationaryImage (F.m i) V (F.cylinderCore i)) :
      (-s,z) ∈ E (negM (a i)) := by
    obtain ⟨p,hp,he⟩ := hs
    refine mem_iUnion.mpr ⟨⟨τ i,hr.index i⟩,p,(F.reflection_cylinderCore hr i).symm ▸ hp,?_⟩
    apply Prod.ext
    · change (F.m (τ i):ℝ)*V p.1 = -s
      rw [hr.index,Int.cast_neg,neg_mul]
      exact congrArg Neg.neg (show (F.m i:ℝ)*V p.1 = s from congrArg Prod.fst he)
    · exact (show p.2 = z from congrArg Prod.snd he)
  have hsE (i : ι) (C : Set ℝ) (a : UnitAddCircle) (s : ℝ)
      (hs : stationaryWeight C (fun x => (F.m i:ℝ)*V x) (F.A₀ i a) s ≠ 0) :
      (s,a) ∈ stationaryImage (F.m i) V (F.cylinderCore i) := by
    obtain ⟨x,hx,hxs⟩ := stationaryWeight_support_subset
      (show support (F.A₀ i a) ⊆ {x | (x,a) ∈ F.cylinderCore i} from
        fun x hx => F.support_subset_cylinderCore i a hx) hs
    exact ⟨(x,a),hx,Prod.ext hxs rfl⟩
  refine ⟨c,hc,h0,χ,fun i => ⟨?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  · exact (hξ (a i)).1.mul ((hξ (negM (a i))).1.comp (contDiff_fst.neg.prodMk contDiff_snd))
  · exact (hξ (a i)).2.1.mul_right
  · exact (hsub i).trans (hξ (a i)).2.2.1
  · intro s z
    exact ⟨mul_nonneg ((hξ (a i)).2.2.2.1 (s,z)).1 ((hξ (negM (a i))).2.2.2.1 (-s,z)).1,
      (mul_le_mul ((hξ (a i)).2.2.2.1 (s,z)).2 ((hξ (negM (a i))).2.2.2.1 (-s,z)).2
        ((hξ (negM (a i))).2.2.2.1 (-s,z)).1 zero_le_one).trans (by norm_num)⟩
  · intro C z s hs
    have hse := hsE i C z s hs
    have h1 := ((hξ (a i)).2.2.2.2 (s,z) (mem_iUnion.mpr ⟨⟨i,rfl⟩,hse⟩)).self_of_nhds
    have h2 := ((hξ (negM (a i))).2.2.2.2 (-s,z) (hre i hse)).self_of_nhds
    change ξ (a i) (s,z) = 1 at h1
    change ξ (negM (a i)) (-s,z) = 1 at h2
    simp only [χ,h1,h2,one_mul]
  · intro i j hij
    exact (hξd (fun h => hij (congrArg Subtype.val h))).mono (hsub i) (hsub j)
  · intro i j hij
    have he : a i = a j := Subtype.ext hij
    simp only [χ,he]
  · intro i s z
    simp only [χ,hneg,hnn,neg_neg,mul_comm]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- A repeated-mode neutral cutoff, independent of the spare coordinate.
Separation is in scalar frequency, not just on the cylinder. -/
theorem scalar_grouped_neutral_cutoffs {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) {τ : ι → ι} (hr : F.Reflection τ) :
    ∃ c : ℕ, 0 < c ∧ (∀ x : ℝ, (c:ℝ)+F.V x ≠ 0) ∧
      ∃ χ : ι → ℝ → ℝ,
        (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
          χ i 0=0 ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
          ∀ (C : Set ℝ) a s, stationaryWeight C
            (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i a) s ≠ 0 → χ i s=1) ∧
        (∀ i j, F.m i ≠ F.m j → Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
        (∀ i j, F.m i=F.m j → χ i=χ j) ∧
        ∀ i s, χ (τ i) s=χ i (-s) := by
  classical
  let m : Option ι → ℤ := fun i => i.elim 1 F.m
  have hm (i : Option ι) : m i ≠ 0 := by
    cases i with
    | none => norm_num [m]
    | some i => exact F.nonzero i
  obtain ⟨c,hc,hc0,hsep⟩ := exists_integral_speed_separation m F.periodic.lift hm F.speed_continuous
  let V : ℝ → ℝ := fun x => (c:ℝ)+F.V x
  have h0 (x : ℝ) : V x ≠ 0 := by simpa [m,V] using hc0 none (x:UnitAddCircle)
  have hV : Continuous V := continuous_const.add F.smooth_speed.continuous
  let M := ↥(range F.m)
  let : Finite M := (finite_range F.m).to_subtype
  let a (i : ι) : M := ⟨F.m i,mem_range_self i⟩
  let negM (k : M) : M := ⟨-k.val,by
    obtain ⟨i,hi⟩ := k.property
    exact ⟨τ i,by simp only [hr.index,hi]⟩⟩
  have hneg (i : ι) : a (τ i)=negM (a i) := Subtype.ext (hr.index i)
  have hnn (k : M) : negM (negM k)=k := Subtype.ext (neg_neg _)
  let E (k : M) := (fun x => (k.val:ℝ)*V x) '' Icc F.l F.u
  have hEc k : IsCompact (E k) := isCompact_Icc.image (continuous_const.mul hV)
  have hEd : Pairwise (Disjoint on E) := by
    intro k l hkl
    obtain ⟨i,hi⟩ := k.property
    obtain ⟨j,hj⟩ := l.property
    apply Set.disjoint_left.mpr
    rintro s ⟨x,_hx,hx⟩ ⟨y,_hy,hy⟩
    have he : (F.m i:ℝ)*((c:ℝ)+F.V x)=(F.m j:ℝ)*((c:ℝ)+F.V y) := by
      rw [hi,hj]; exact hx.trans hy.symm
    exact hkl (Subtype.ext (hi.symm.trans ((hsep (some i) (some j) (x:UnitAddCircle) (y:UnitAddCircle) he).trans hj)))
  have hEU k : E k ⊆ ({0}:Set ℝ)ᶜ := by
    rintro s ⟨x,_hx,rfl⟩ hs
    obtain ⟨i,hi⟩ := k.property
    exact mul_ne_zero (by rw [← hi]; exact_mod_cast F.nonzero i) (h0 x) hs
  obtain ⟨ξ,hξ,hξd⟩ := finite_disjoint_frequency_cutoffs E (fun _ => ({0}:Set ℝ)ᶜ)
    hEc (fun _ => isOpen_compl_singleton) hEU hEd
  let χ : ι → ℝ → ℝ := fun i s => ξ (a i) s*ξ (negM (a i)) (-s)
  have hsub i : tsupport (χ i) ⊆ tsupport (ξ (a i)) := tsupport_mul_subset_left
  have hre (k : M) {s : ℝ} (hs : s ∈ E k) : -s ∈ E (negM k) := by
    obtain ⟨x,hx,rfl⟩ := hs
    exact ⟨x,hx,by simp only [negM,Int.cast_neg,neg_mul]⟩
  refine ⟨c,hc,h0,χ,fun i => ⟨?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  · exact (hξ (a i)).1.mul ((hξ (negM (a i))).1.comp contDiff_id.neg)
  · exact (hξ (a i)).2.1.mul_right
  · by_contra hn
    exact (hξ (a i)).2.2.1 (hsub i (subset_tsupport (χ i) hn)) rfl
  · intro s
    exact ⟨mul_nonneg ((hξ (a i)).2.2.2.1 s).1 ((hξ (negM (a i))).2.2.2.1 (-s)).1,
      (mul_le_mul ((hξ (a i)).2.2.2.1 s).2 ((hξ (negM (a i))).2.2.2.1 (-s)).2
        ((hξ (negM (a i))).2.2.2.1 (-s)).1 zero_le_one).trans (by norm_num)⟩
  · intro C z s hs
    have he : s ∈ E (a i) := stationaryWeight_support_subset
      ((F.support_lift i z).trans Ioc_subset_Icc_self) hs
    have h1 := ((hξ (a i)).2.2.2.2 s he).self_of_nhds
    have h2 := ((hξ (negM (a i))).2.2.2.2 (-s) (hre _ he)).self_of_nhds
    change ξ (a i) s=1 at h1
    change ξ (negM (a i)) (-s)=1 at h2
    simp only [χ,h1,h2,one_mul]
  · intro i j hij
    exact (hξd (fun h => hij (congrArg Subtype.val h))).mono (hsub i) (hsub j)
  · intro i j hij
    have he : a i=a j := Subtype.ext hij
    simp only [χ,he]
  · intro i s
    simp only [χ,hneg,hnn,neg_neg,mul_comm]

end ThreeTorus
end
end

end OAI
