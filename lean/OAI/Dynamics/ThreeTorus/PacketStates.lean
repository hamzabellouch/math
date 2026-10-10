import OAI.Dynamics.ThreeTorus.PassageFamilies

namespace OAI

/-! Closed finite packet states, canonical densities, residue reindexing, anchors, reflection, clipping, and state tracking. -/

section

/-! Concrete finite-packet input data and the support bookkeeping used by
iteration. Field regularity is inherited from literal amplitudes. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

def core (i : ι) : Set ℝ := tsupport (F.A₀ i 0)

lemma core_subset (i : ι) : F.core i ⊆ Icc F.l F.u :=
  closure_minimal ((F.support_lift i 0).trans Ioc_subset_Icc_self) isClosed_Icc

lemma core_compact (i : ι) : IsCompact (F.core i) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (F.core_subset i)

lemma support_subset_core (hmod : F.SpareIndependent) (i : ι) (a : UnitAddCircle) :
    support (F.A₀ i a) ⊆ F.core i := by
  intro x hx
  apply subset_tsupport _
  intro hz
  apply hx
  apply norm_eq_zero.mp
  rw [hmod.1 i a x,hz,norm_zero]

lemma amplitude_bound [Finite ι] : ∃ B : ℝ, 0 ≤ B ∧ ∀ i p, ‖F.A i p‖^2 ≤ B := by
  classical
  have hb i := (isCompact_range ((F.continuous_amplitude i).norm.pow 2)).isBounded.exists_norm_le
  choose B hB using hb
  obtain ⟨C,hC⟩ := (Set.finite_range B).isCompact.isBounded.exists_norm_le
  refine ⟨max C 0,le_max_right _ _,fun i p => ?_⟩
  have h₁ := hB i _ (mem_range_self p)
  have h₂ := hC _ (mem_range_self i)
  exact (le_abs_self _).trans (h₁.trans ((le_abs_self _).trans (h₂.trans (le_max_left _ _))))

/-- Adding an integral carrier changes no temporal eigenfrequency modulo one. -/
def carrier (c : ℤ) : PassagePackets ι := { F with
  V := fun x => (c:ℝ)+F.V x
  periodic := fun x => by dsimp; rw [F.periodic x]
  smooth_speed := contDiff_const.add F.smooth_speed
  positive_deriv := fun x hx => by
    simpa only [deriv_const_add] using F.positive_deriv x hx }

lemma carrier_spare (c : ℤ) (hmod : F.SpareIndependent) :
    (F.carrier c).SpareIndependent := hmod

lemma carrier_circle (c : ℤ) (x : ℝ) :
    ((F.carrier c).V x:UnitAddCircle) = (F.V x:UnitAddCircle) := by
  change (((c:ℝ)+F.V x:ℝ):UnitAddCircle) = _
  rw [AddCircle.coe_add]
  have hc : ((c:ℝ):UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).mpr ⟨c,by simp⟩
  rw [hc,zero_add]

/-- Scalar cutoffs with arbitrarily small support tracking error exist for
EVERY sufficiently large carrier.  Choosing the carrier is therefore still
compatible with the signal-law and normalized-index error bounds. -/
theorem tracked_cutoffs [Finite ι] (hi : Injective F.m)
    (hmod : F.SpareIndependent) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ c : ℕ in atTop, 0 < c ∧ ∃ χ : ι → ℝ → ℝ,
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        χ i 0 = 0 ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        (∀ s ∈ tsupport (χ i), ∃ x ∈ F.core i, |s-(F.m i:ℝ)*((c:ℝ)+F.V x)| < η) ∧
        ∀ (C : Set ℝ) a s, stationaryWeight C
          (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i a) s ≠ 0 → χ i s = 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) := by
  have hv : Continuous F.periodic.lift := by
    apply Continuous.quotient_lift
    exact F.smooth_speed.continuous
  filter_upwards [eventually_integral_speed_separation F.m F.periodic.lift F.nonzero hv] with c hc
  have hzero i : 0 ∉ (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) '' F.core i := by
    rintro ⟨x,_hx,he⟩
    exact hc.2.1 i (x:UnitAddCircle) he
  have hsep : Pairwise (fun i j => Disjoint
      ((fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) '' F.core i)
      ((fun x => (F.m j:ℝ)*((c:ℝ)+F.V x)) '' F.core j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro s ⟨x,_hx,rfl⟩ ⟨y,_hy,he⟩
    exact hij (hi (hc.2.2 i j (x:UnitAddCircle) (y:UnitAddCircle) he.symm))
  obtain ⟨χ,hχ,hd⟩ := tracked_frequency_cutoffs F.m (fun x => (c:ℝ)+F.V x) F.core
    (continuous_const.add F.smooth_speed.continuous) F.core_compact hzero hsep hη
  exact ⟨hc.1,χ,fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1,
    (hχ i).2.2.2.1,(hχ i).2.2.2.2.2.1,fun C a s =>
      (hχ i).2.2.2.2.2.2 C (F.A₀ i a) (F.support_subset_core hmod i a) s⟩,hd⟩

end PassagePackets
end ThreeTorus
end
end

section

/-! Canonical smooth density of a literal passage-state packet.  These are
computed from the actual amplitude and speed; no spectral property is a field. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma continuous_density_unique {p q : UnitAddCircle → ℝ}
    (hp : Continuous p) (hq : Continuous q) (hp0 : ∀ z, 0 ≤ p z) (hq0 : ∀ z, 0 ≤ q z)
    (he : AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (p z)) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (q z))) : p = q := by
  apply (Continuous.ae_eq_iff_eq AddCircle.haarAddCircle hp hq).mp
  have hh := (withDensity_eq_iff_of_sigmaFinite
    hp.measurable.ennreal_ofReal.aemeasurable hq.measurable.ennreal_ofReal.aemeasurable).mp he
  filter_upwards [hh] with z hz
  have hh := congrArg ENNReal.toReal hz
  simpa only [ENNReal.toReal_ofReal (hp0 z), ENNReal.toReal_ofReal (hq0 z)] using hh

lemma fold_density_nonzero {q : ℝ → ℝ} {z : UnitAddCircle}
    (hz : foldCircleDensity q z ≠ 0) : ∃ s : ℝ, (s:UnitAddCircle) = z ∧ q s ≠ 0 := by
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective z
  rw [foldCircleDensity_coe_all] at hz
  have hk : ∃ k : ℤ, q (x+k) ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hz (by simp only [hh,tsum_zero])
  obtain ⟨k,hk⟩ := hk
  refine ⟨x+k,?_,hk⟩
  rw [AddCircle.coe_add]
  have he : ((k:ℝ):UnitAddCircle) = 0 := (AddCircle.coe_eq_zero_iff 1).mpr ⟨k,by simp⟩
  rw [he,add_zero]

lemma foldCircleDensity_finsetSum_eq {ι : Type*} (S : Finset ι) (q : ι → ℝ → ℝ)
    (hq : ∀ i ∈ S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (q i))
    (hc : ∀ i ∈ S, HasCompactSupport (q i)) :
    foldCircleDensity (fun x => ∑ i ∈ S, q i x) =
      fun z => ∑ i ∈ S, foldCircleDensity (q i) z := by
  have hqS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∑ i ∈ S, q i x) := ContDiff.sum hq
  have hcS : HasCompactSupport (fun x => ∑ i ∈ S, q i x) := by
    convert HasCompactSupport.finset_sum hc using 1
    funext point
    simp only [Finset.sum_apply]
  apply (Continuous.ae_eq_iff_eq AddCircle.haarAddCircle
    (continuous_of_continuous_lift (foldCircleDensity_smooth_lift hqS hcS).continuous)
    (continuous_finsetSum _ (fun i hi => continuous_of_continuous_lift
      (foldCircleDensity_smooth_lift (hq i hi) (hc i hi)).continuous))).mp
  exact foldCircleDensity_finsetSum_ae S q
    (fun i hi => (hq i hi).continuous.measurable)
    (fun i hi => (hq i hi).continuous.integrable_of_hasCompactSupport (hc i hi))

namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

def weight (i : ι) : ℝ → ℝ :=
  stationaryWeight (Icc (F.l-F.R) (F.u+F.R)) (fun x => (F.m i:ℝ)*F.V x) (F.A₀ i 0)

def density (i : ι) : UnitAddCircle → ℝ := foldCircleDensity (F.weight i)

lemma weight_nonneg (i : ι) (s : ℝ) : 0 ≤ F.weight i s :=
  branchDensity_nonneg (fun _ => sq_nonneg _) s

lemma density_nonneg (i : ι) (z : UnitAddCircle) : 0 ≤ F.density i z :=
  foldCircleDensity_nonneg (F.weight_nonneg i) z

lemma smooth_zero_lift (i : ι) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F.A₀ i 0) := by
  simpa only [Function.comp_def, AddCircle.coe_zero] using
    (F.smooth_lift i).comp (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => (x,(0:ℝ))) from contDiff_id.prodMk contDiff_const)

lemma weight_regular (i : ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F.weight i) ∧ HasCompactSupport (F.weight i) := by
  let q := fun x => ‖F.A₀ i 0 x‖^2
  have hqs : tsupport q ⊆ F.core i := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp [q,hz])
  have hqc : HasCompactSupport q := (F.core_compact i).of_isClosed_subset isClosed_closure hqs
  have hs : tsupport q ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.core_subset i (hqs hx)
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have has : support (F.A₀ i 0) ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.support_lift i 0 hx
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have he := stationaryWeight_change_branch Ioo_subset_Icc_self hb.1 has
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (stationaryWeight _ _ _) ∧ HasCompactSupport (stationaryWeight _ _ _)
  rw [he]
  exact ⟨branchDensity_smooth (contDiff_const.mul F.smooth_speed) isOpen_Ioo
    (hb.1.mono Ioo_subset_Icc_self) hb.2 ((F.smooth_zero_lift i).norm_sq (𝕜 := ℂ)) hqc hs,
    branchDensity_compact (continuous_const.mul F.smooth_speed.continuous) hqc⟩

lemma density_smooth (i : ι) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : ℝ => F.density i (x:UnitAddCircle)) :=
  foldCircleDensity_smooth_lift (F.weight_regular i).1 (F.weight_regular i).2

lemma density_continuous (i : ι) : Continuous (F.density i) :=
  continuous_of_continuous_lift (F.density_smooth i).continuous

lemma speed_continuous : Continuous F.periodic.lift := by
  apply Continuous.quotient_lift
  exact F.smooth_speed.continuous

/-- The canonical density is the spectral measure of the actual angular packet. -/
theorem density_spectral (hmod : F.SpareIndependent) (i : ι) :
    packetSpectralMeasure (fun u => (F.periodic.lift u:UnitAddCircle)) (F.m i) (F.A i) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (F.density i z)) := by
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have hs : support (F.A₀ i 0) ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.support_lift i 0 hx
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have he := oldPacket_spectralDensity_of_modulus (m := F.m i) (c := 0) (v := F.periodic.lift)
    (F.continuous_amplitude i) (F.smooth_zero_lift i).continuous (hmod.2 i)
    (F.lift_matches i 0) ((F.support_lift i 0).trans (by
      intro x hx; exact ⟨lt_of_le_of_lt F.lo hx.1, hx.2.trans F.uo⟩)) hs
    F.speed_continuous.measurable F.smooth_speed (fun _ _ => rfl)
    isOpen_Ioo Ioo_subset_Icc_self hb.1 hb.2
  simpa only [Int.cast_zero,sub_zero,density,weight] using he

lemma density_marginal (hmod : F.SpareIndependent) (i : ι) :
    foldCircleDensity (fun s => ∫ a, stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
      (fun x => (F.m i:ℝ)*F.V x) (F.A₀ i a) s ∂AddCircle.haarAddCircle) = F.density i := by
  congr 1
  funext s
  simp [stationaryWeight_modulus_independent (hmod.1 i),weight]

lemma density_carrier (hmod : F.SpareIndependent) (c : ℤ) (i : ι) :
    (F.carrier c).density i = F.density i := by
  apply continuous_density_unique ((F.carrier c).density_continuous i) (F.density_continuous i)
    ((F.carrier c).density_nonneg i) (F.density_nonneg i)
  rw [← (F.carrier c).density_spectral (F.carrier_spare c hmod) i,← F.density_spectral hmod i]
  congr 1
  funext z
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective z
  exact F.carrier_circle c x

/-- A nonzero density value is realized on the true old amplitude support,
not merely in the convex hull of its frequency range. -/
lemma density_support (i : ι) {z : UnitAddCircle} (hz : F.density i z ≠ 0) :
    ∃ x ∈ support (F.A₀ i 0), ((F.m i:ℝ)*F.V x:UnitAddCircle) = z := by
  obtain ⟨s,hs,hq⟩ := fold_density_nonzero hz
  have hy : s ∈ (fun x => (F.m i:ℝ)*F.V x) '' Icc (F.l-F.R) (F.u+F.R) := by
    by_contra hh
    exact hq (by simp [weight,stationaryWeight,branchDensity,hh])
  let x := invFunOn (fun x => (F.m i:ℝ)*F.V x) (Icc (F.l-F.R) (F.u+F.R)) s
  have hx := invFunOn_pos hy
  refine ⟨x,?_,?_⟩
  · intro hz
    change F.A₀ i 0 (invFunOn (fun x => (F.m i:ℝ)*F.V x)
      (Icc (F.l-F.R) (F.u+F.R)) s) = 0 at hz
    exact hq (by simp [weight,stationaryWeight,branchDensity,hy,hz])
  · exact (congrArg (fun t : ℝ => (t:UnitAddCircle)) hx.2).trans hs

end PassagePackets
end ThreeTorus
end
end

section

/-! Exact identification of the canonical density of an iterated packet state
with the literal finite density already controlled by the passage estimates. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma exactRetainedPacketDensity_nonneg (I : Set ℝ) (J : ℝ → ℝ) (ψ : UnitAddCircle → ℝ)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S : Finset ℤ) (n : ℕ) (z : UnitAddCircle) :
    0 ≤ exactRetainedPacketDensity I J ψ χ m H A S n z := by
  apply foldCircleDensity_nonneg
  intro t
  apply Finset.sum_nonneg
  intro j _hj
  exact unfoldedModeDensity_nonneg
    (circleDensityLift_nonneg (retainedCircleWeight_nonneg ψ χ _ n j) 0) (Nat.cast_nonneg n) j t

lemma exactRetainedPacketDensity_singleton (I : Set ℝ) (J : ℝ → ℝ) (ψ : UnitAddCircle → ℝ)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (j : ℤ) (n : ℕ) :
    exactRetainedPacketDensity I J ψ χ m H A {j} n =
      foldCircleDensity (unfoldedModeDensity I J (invFunOn J I) (deriv J)
        (circleDensityLift 0 (retainedCircleWeight ψ χ
          (fun n j => exactPassageCoeff m (H n) A j) n j)) n j) := by
  simp only [exactRetainedPacketDensity,Finset.sum_singleton]

lemma exactRetainedPacketDensity_sum_singletons
    {I : Set ℝ} {J : ℝ → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {m : ℤ}
    {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {S : Finset ℤ} {n : ℕ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hc : HasCompactSupport ψ₀)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1) ∩ I)
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (hn : 0 < n) (hS : ∀ j ∈ S, j ≠ 0) :
    exactRetainedPacketDensity I J ψ χ m H A S n =
      fun z => ∑ j ∈ S, exactRetainedPacketDensity I J ψ χ m H A {j} n z := by
  unfold exactRetainedPacketDensity
  simp only [Finset.sum_singleton]
  simp_rw [retainedWeight_lift_eq χ m H A n _ he (hs.trans inter_subset_left)]
  apply foldCircleDensity_finsetSum_eq
  · intro j _hj
    exact unfoldedModeDensity_smooth hJ hIo hinj hd
      (realRetainedWeight_smooth hψ hχ hHl hH hA n j)
      (realRetainedWeight_compact hc χ m H A n j)
      ((realRetainedWeight_support ψ₀ χ m H A n j).trans (hs.trans inter_subset_right)) n j
  · intro j hj
    exact unfoldedModeDensity_compact hJ.continuous
      (realRetainedWeight_compact hc χ m H A n j)
      (by exact_mod_cast hn.ne') (by exact_mod_cast hS j hj)

lemma exactRetainedPacketDensity_filtered_singletons
    {I : Set ℝ} {J : ℝ → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {m : ℤ}
    {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ} {S : Finset ℤ} {n : ℕ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hc : HasCompactSupport ψ₀)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1) ∩ I)
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (hn : 0 < n) (hS : ∀ j ∈ S, j ≠ 0) (E : ℤ → Prop) [DecidablePred E] :
    exactRetainedPacketDensity I J ψ χ m H A (S.filter E) n =
      fun z => ∑ j : ↥S, if E j.val then
        exactRetainedPacketDensity I J ψ χ m H A {j.val} n z else 0 := by
  rw [exactRetainedPacketDensity_sum_singletons hJ hIo hinj hd hψ hc he hs hχ hHl hH hA hn
    (fun j hj => hS j (Finset.mem_filter.mp hj).1)]
  funext z
  rw [Finset.sum_filter]
  exact (Finset.sum_coe_sort S (fun j => if E j then
    exactRetainedPacketDensity I J ψ χ m H A {j} n z else 0)).symm

/-- Pointwise, not just a.e., identity of a literal output packet's canonical
density. The hypotheses below are only smooth lifts and the displayed literal
coefficient/speed identities; no new spectral law is assumed. -/
theorem literal_packet_canonical_density {ι : Type*} (F : PassagePackets ι)
    (hmod : F.SpareIndependent) (i : ι)
    {I : Set ℝ} {J : UnitAddCircle → ℝ} {J₀ : ℝ → ℝ}
    {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m j : ℤ} {n : ℕ} {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hm : F.m i = j) (hamp : F.A i = retainedAmplitude ψ χ m H A n j)
    (hspeed : ∀ a, (F.periodic.lift a:UnitAddCircle) = (((1+J a/n)/n:ℝ):UnitAddCircle))
    (hJc : Continuous J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hψc : Continuous ψ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀)
    (hc : HasCompactSupport ψ₀)
    (he : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = ψ₀ x)
    (hs : tsupport ψ₀ ⊆ Ioc (0:ℝ) (0+1) ∩ I)
    (hχc : Continuous χ.uncurry) (hχ : CylinderSmooth χ.uncurry)
    (hHc : ∀ n, Continuous (H n))
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hAc : Continuous A)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (hn : 0 < n) :
    F.density i = exactRetainedPacketDensity I J₀ ψ χ m H A {j} n := by
  have hj : j ≠ 0 := hm ▸ F.nonzero i
  have hps := exactRetainedPacketDensity_smooth_lift (m := m) hJ hIo hinj hd hψ hc he hs hχ hHl hH hA hn
    (S := {j}) (fun k hk => by simpa only [Finset.mem_singleton.mp hk] using hj)
  apply continuous_density_unique (F.density_continuous i)
    (continuous_of_continuous_lift hps.continuous) (F.density_nonneg i)
    (exactRetainedPacketDensity_nonneg I J₀ ψ χ m H A {j} n)
  rw [← F.density_spectral hmod i,hm,hamp,show
    (fun a => (F.periodic.lift a:UnitAddCircle)) =
      (fun a => (((1+J a/n)/n:ℝ):UnitAddCircle)) from funext hspeed,
    exactRetainedPacketDensity_singleton]
  exact retainedAmplitude_spectralDensity hψc hχc hHc hAc
    (fun x hx hp => (hs (subset_tsupport ψ₀ (by rwa [he x hx] at hp))).2)
    hJc.measurable hJ hJe hIo hinj hd hn hj

end ThreeTorus
end
end

section

/-! The residue slices are slices of the actual retained angular list, not
independently fabricated Fourier arrays. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma sum_residue_rename {M : Type*} [AddCommMonoid M]
    (f : ℤ → M) (S T : Finset ℤ) (Q h : ℤ) (hQ : Q ≠ 0)
    (hS : ∀ k, k ∉ S → f (h+k*Q) = 0) (hT : ∀ j, j ∉ T → f j = 0) :
    ∑ k ∈ S, f (h+k*Q) = ∑ j ∈ T.filter (fun j => j % Q = h % Q), f j := by
  classical
  let a : ℤ → ℤ := fun k => h+k*Q
  have hai : Injective a := fun x y he => mul_right_cancel₀ hQ (add_left_cancel he)
  let F : ℤ → M := fun j => if j % Q = h % Q then f j else 0
  have hFa k : F (a k) = f (a k) := by simp [F,a,Int.add_mul_emod_self_right]
  have hSa j (hj : j ∉ S.image a) : F j = 0 := by
    dsimp only [F]
    split_ifs with he
    · let k := j/Q-h/Q
      have hk : a k = j := by
        dsimp [a,k]
        have hh := Int.emod_add_ediv_mul h Q
        have hj' := Int.emod_add_ediv_mul j Q
        rw [he] at hj'
        nlinarith
      have hkS : k ∉ S := fun hks => hj (hk ▸ Finset.mem_image.mpr ⟨k,hks,rfl⟩)
      rw [← hk]
      exact hS k hkS
    · rfl
  have hTF j (hj : j ∉ T) : F j = 0 := by simp [F,hT j hj]
  calc
    ∑ k ∈ S, f (a k) = ∑ k ∈ S, F (a k) := by simp_rw [hFa]
    _ = ∑ j ∈ S.image a, F j := (Finset.sum_image hai.injOn).symm
    _ = ∑ j ∈ T, F j := sum_eq_of_zero_off F (S.image a) T hSa hTF
    _ = _ := (Finset.sum_filter _ f).symm

lemma exactRetainedPacketDensity_residue_rename
    (I : Set ℝ) (J₀ : ℝ → ℝ) (ψ : UnitAddCircle → ℝ)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S T : Finset ℤ) (n : ℕ)
    (Q h : ℤ) (hQ : Q ≠ 0)
    (hS : ∀ k, k ∉ S → ∀ a, χ (((h+k*Q:ℤ):ℝ)/n) a = 0)
    (hT : ∀ j, j ∉ T → ∀ a, χ ((j:ℝ)/n) a = 0) :
    foldCircleDensity (fun t => ∑ k ∈ S,
      unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
        (circleDensityLift 0 (retainedCircleWeight ψ χ
          (fun n j => exactPassageCoeff m (H n) A j) n (h+k*Q)))
        n ((h+k*Q:ℤ):ℝ) t) =
      exactRetainedPacketDensity I J₀ ψ χ m H A (T.filter (fun j => j % Q = h % Q)) n := by
  unfold exactRetainedPacketDensity
  congr 1
  funext t
  apply sum_residue_rename
    (fun j : ℤ => unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
      (circleDensityLift 0 (retainedCircleWeight ψ χ
        (fun n j => exactPassageCoeff m (H n) A j) n j)) n (j:ℝ) t) S T Q h hQ
  · intro k hk
    have hz := hS k hk
    simp only [Int.cast_add,Int.cast_mul] at hz
    simp [unfoldedModeDensity,scaledBranchKernel,branchDensity,
      circleDensityLift,retainedCircleWeight,hz]
  · intro j hj
    simp [unfoldedModeDensity,scaledBranchKernel,branchDensity,
      circleDensityLift,retainedCircleWeight,hT j hj]

end ThreeTorus
end
end

section

/-! Neutral refresh splits the literal next angular list, simultaneously for
all residues, with total error independent of the number of residue tests. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma foldCircleDensity_const_mul (w : ℝ → ℝ) (c : ℝ) :
    foldCircleDensity (fun s => c*w s) = fun z => c*foldCircleDensity w z := by
  funext z
  induction z using Quotient.inductionOn with | h x =>
    simp only [foldCircleDensity_coe_all,tsum_mul_left]

theorem exact_neutral_residue_refresh
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {Δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+Δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hΔt : Tendsto Δ atTop (𝓝 0))
    {v : UnitAddCircle → ℝ} (hv : Measurable v) (hVe : ∀ x : ℝ, v (x:UnitAddCircle) = V x)
    {B : ℝ} (hB : 0 ≤ B) (hAb : ∀ p, ‖A p‖^2 ≤ B)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {χ : ℝ → UnitAddCircle → ℝ}
    (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry) (hzχ : ∀ a, χ 0 a = 0)
    (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
    {Q : ℕ} (hQ : 0 < Q) :
    let pold := foldCircleDensity (fun s => ∫ a, stationaryWeight (Icc (l-R) (u+R))
      (fun x => (m:ℝ)*V x) (A₀ a) s ∂AddCircle.haarAddCircle)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ β : ℝ,
      ∀ T : ℕ → Finset ℤ,
      (∀ n, 0 < n → ∀ j ∈ T n, j ≠ 0) →
      (∀ n, 0 < n → ∀ j ∉ T n, ∀ a, χ ((j:ℝ)/n) a = 0) →
      ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
        (∑ h : Fin Q, ∫ z,
          |exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal c L β)
            (neutralCircleCutoff c) χ m H A
            ((T n).filter (fun j => j % (Q:ℤ) = (h.val:ℤ) % (Q:ℤ))) n z-
            (Q:ℝ)⁻¹*pold z| ∂AddCircle.haarAddCircle) < C/L+4*δ*B+η := by
  classical
  dsimp only
  let ψ := neutralCircleCutoff c
  let W := fun s a => stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s
  let pold := foldCircleDensity (fun s => ∫ a, W s a ∂AddCircle.haarAddCircle)
  let pcut := foldCircleDensity (fun s => ∫ a, stationaryWeight (Icc (l-R) (u+R))
    (fun x => (m:ℝ)*V x) (fun x => (ψ a:ℂ)*A₀ a x) s ∂AddCircle.haarAddCircle)
  let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
    (fun p : ℝ × ℝ => A₀ (p.2:UnitAddCircle) p.1) c.ψ
  have hψc := continuous_neutralCircleCutoff c
  have hψs : tsupport c.ψ ⊆ Ioc (0:ℝ) (0+1) ∩ Ioo δ (1-δ) := by
    intro x hx
    have hh := c.ψ_support hx
    exact ⟨⟨by linarith [hh.1],by linarith [hh.2]⟩,hh⟩
  have heψ : ∀ x ∈ Ioc (0:ℝ) (0+1), c.ψ x = ψ (x:UnitAddCircle) := by
    intro x hx
    exact (lawPsi_eq c hδ ⟨hx.1.le,by simpa using hx.2⟩).symm
  have hcut : (∫ z, |pcut z-pold z| ∂AddCircle.haarAddCircle) ≤ B*(4*δ) := by
    have hs₁ : ∀ a, support (A₀ a) ⊆ Ioc o (o+1) := by
      intro a x hx
      have hh := hsupp a hx
      exact ⟨lt_of_le_of_lt hlo hh.1,hh.2.trans huo⟩
    have hs₂ : ∀ a, support (A₀ a) ⊆ Ioo (l-R) (u+R) := by
      intro a x hx
      have hh := hsupp a hx
      exact ⟨by linarith [hh.1],by linarith [hh.2]⟩
    have hb := oldStationaryMarginal_cutoff_l1 hAcont hAc hA hs₁ hs₂ hv hV
      (fun x _ => hVe x) isOpen_Ioo Ioo_subset_Icc_self
      (scaled_speed_good_branch hm hR hV hdV).1 (scaled_speed_good_branch hm hR hV hdV).2
      hψc (neutralCircleCutoff_bounds c hδ) hB hAb
    exact hb.trans (mul_le_mul_of_nonneg_left (neutralCircleCutoff_error c hδ hδ') hB)
  have hmarg : (fun s => ∫ a, F (a,s)) = fun s => ∫ a,
      stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
        (fun x => (ψ a:ℂ)*A₀ a x) s ∂AddCircle.haarAddCircle := by
    funext s
    exact stationaryCutoffLift_marginal heψ
      (fun x hx => (hψs (subset_tsupport c.ψ hx)).1) _ _ s
  have hsp (h : Fin Q) := exact_neutral_circle_spectral_estimate hm hH hA hA₀ hAc hAd hAr
    hsupp hlo huo hlu hR hPr hV hPV hdV h0 hHc hAcont hΔt isOpen_Ioo
    c.ψ_smooth c.ψ_compact hψs heψ hψc hχc hcχ hzχ
    (neutralCircleCutoff_bounds c hδ) hχ hχW hQ (h.val:ℤ)
  choose C hC hrest using hsp
  refine ⟨∑ h, C h,Finset.sum_nonneg (fun h _ => hC h),?_⟩
  intro L hL β T hTN hTZ η hη
  have hJs := neutralJitterReal_smooth c L β
  have hJc := continuous_neutralJitter c L β
  have heJ : ∀ a ∈ Ioo δ (1-δ), neutralJitterReal c L β a = L*a+β :=
    fun a ha => neutralJitterReal_affine c hδ L β ⟨ha.1.le,ha.2.le⟩
  have hJinj : InjOn (neutralJitterReal c L β) (Ioo δ (1-δ)) := by
    intro a ha b hb hab
    rw [heJ a ha,heJ b hb] at hab
    nlinarith
  have hJd : ∀ a ∈ Ioo δ (1-δ), deriv (neutralJitterReal c L β) a ≠ 0 := by
    intro a ha
    rw [neutralJitterReal_deriv c hδ L β ha]
    exact hL.ne'
  choose S hSN hST ht using fun h => hrest h L hL β (neutralJitterReal c L β)
    (neutralJitter c L β) heJ hJs hJc.measurable (fun x _ => neutralJitter_coe c L β x)
  have hpcuti : Integrable pcut AddCircle.haarAddCircle := by
    have hreg := exact_cutoff_weight_regular hm hR hV hdV hAr
      (fun a => (hsupp a).trans Ioc_subset_Icc_self) c.ψ_smooth c.ψ_compact h0
    have hi := compact_slice_integral_regular
      ((hreg.1.comp (contDiff_snd.prodMk contDiff_fst)).continuous)
      (hreg.2.1.comp_homeomorph (Homeomorph.prodComm ℝ ℝ))
    dsimp only [pcut]
    rw [← hmarg]
    exact integrable_foldCircleDensity hi.1.measurable hi.2
  have hpoldi : Integrable pold AddCircle.haarAddCircle := by
    have hs₁ : ∀ a, support (A₀ a) ⊆ Ioc o (o+1) := fun a x hx =>
      ⟨lt_of_le_of_lt hlo (hsupp a hx).1,(hsupp a hx).2.trans huo⟩
    have hs₂ : ∀ a, support (A₀ a) ⊆ Ioo (l-R) (u+R) := by
      intro a x hx
      have hh := hsupp a hx
      exact ⟨by linarith [hh.1],by linarith [hh.2]⟩
    exact (oldStationaryMarginal_map hAcont hAc hA hs₁ hs₂ hv hV
      (fun x _ => hVe x) isOpen_Ioo Ioo_subset_Icc_self
      (scaled_speed_good_branch hm hR hV hdV).1 (scaled_speed_good_branch hm hR hV hdV).2).1
  have hQr : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hQz : (Q:ℤ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hqpos : 0 < (Q:ℝ)⁻¹ := inv_pos.mpr hQr
  have hsall := (Filter.eventually_all).mpr (fun h => ht h (η/Q) (div_pos hη hQr))
  filter_upwards [hsall,eventually_gt_atTop (0:ℕ)] with n hnsp hn
  have hp (h : Fin Q) := exactRetainedPacketDensity_integrable (m := m) hJs isOpen_Ioo hJinj hJd
    hψc hχc hHc hAcont hn
    (fun j (hj : j ∈ (T n).filter (fun j => j % (Q:ℤ) = (h.val:ℤ) % (Q:ℤ))) =>
      hTN n hn j (Finset.mem_filter.mp hj).1)
  have hps (h : Fin Q) :
      (∫ z, |exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal c L β)
        ψ χ m H A ((T n).filter (fun j => j % (Q:ℤ) = (h.val:ℤ) % (Q:ℤ))) n z-
        (Q:ℝ)⁻¹*pcut z| ∂AddCircle.haarAddCircle) < C h/L+η/Q := by
    have he := exactRetainedPacketDensity_residue_rename (Ioo δ (1-δ))
      (neutralJitterReal c L β) ψ χ m H A (S h n) (T n) n (Q:ℤ) (h.val:ℤ) hQz
      (hST h n hn) (hTZ n hn)
    have hh := hnsp h
    rw [he,foldCircleDensity_const_mul,hmarg] at hh
    exact hh
  have hcscale : (∫ z, |(Q:ℝ)⁻¹*pcut z-(Q:ℝ)⁻¹*pold z|
      ∂AddCircle.haarAddCircle) ≤ (Q:ℝ)⁻¹*(B*(4*δ)) := by
    simp_rw [← mul_sub,abs_mul,abs_of_pos hqpos]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hcut hqpos.le
  have hfinal (h : Fin Q) :
      (∫ z, |exactRetainedPacketDensity (Ioo δ (1-δ)) (neutralJitterReal c L β)
        ψ χ m H A ((T n).filter (fun j => j % (Q:ℤ) = (h.val:ℤ) % (Q:ℤ))) n z-
        (Q:ℝ)⁻¹*pold z| ∂AddCircle.haarAddCircle) < C h/L+(4*δ*B+η)/Q := by
    have hh := integral_abs_sub_triangle (hp h)
      (hpcuti.const_mul (Q:ℝ)⁻¹) (hpoldi.const_mul (Q:ℝ)⁻¹)
    have hs := hps h
    calc
      _ ≤ _ := hh
      _ < C h/L+η/Q+(Q:ℝ)⁻¹*(B*(4*δ)) := add_lt_add_of_lt_of_le hs hcscale
      _ = _ := by ring
  calc
    _ < ∑ h : Fin Q, (C h/L+(4*δ*B+η)/Q) := by
      apply Finset.sum_lt_sum
      · exact fun h _ => (hfinal h).le
      · exact ⟨⟨0,hQ⟩,Finset.mem_univ _,hfinal ⟨0,hQ⟩⟩
    _ = _ := by
      rw [Finset.sum_add_distrib,← Finset.sum_div]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp
      ring

end ThreeTorus
end
end

section

/-! The simultaneous neutral passage with an actual integer-rounded common
primitive. Its complete geometry and all spectral estimates are supplied by
one and the same sequence of smooth Haar-preserving maps. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

/-- The jitter, all packet lists and all cutoffs are fixed before the final
passage integer. No primitive, convergence, or spectral data are assumed. -/
theorem exists_simultaneous_neutral_residue_passage {ι : Type*} [Fintype ι]
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} {A₀ : ι → UnitAddCircle → ℝ → ℂ}
    {V : ℝ → ℝ} {m : ι → ℤ} {o l u R : ℝ}
    (hm : ∀ i, m i ≠ 0)
    (hA : ∀ i a x, x ∈ Ioc o (o+1) → A i ((x : UnitAddCircle),a) = A₀ i a x)
    (hA₀ : ∀ i a, ContDiff ℝ 2 (A₀ i a)) (hAc : ∀ i, Continuous (A₀ i).uncurry)
    (hAd : ∀ i, Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ i p.1) p.2))
    (hAr : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ i (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ i a, support (A₀ i a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hp : Periodic V 1) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : ∀ i, 0 ∉ (fun x => (m i:ℝ)*V x) '' Icc l u)
    (hAcont : ∀ i, Continuous (A i))
    (hAs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A i (p.1,p.2)))
    {B : ι → ℝ} (hB : ∀ i, 0 ≤ B i) (hAb : ∀ i p, ‖A i p‖^2 ≤ B i)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {χ : ι → ℝ → UnitAddCircle → ℝ}
    (hχs : ∀ i, CylinderSmooth (χ i).uncurry)
    (hχc : ∀ i, Continuous (χ i).uncurry) (hcχ : ∀ i, HasCompactSupport (χ i).uncurry)
    (hzχ : ∀ i a, χ i 0 a = 0) (hχ : ∀ i s a, 0 ≤ χ i s a ∧ χ i s a ≤ 1)
    (hχW : ∀ i s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m i:ℝ)*V x)
      (A₀ i a) s ≠ 0 → χ i s a = 1)
    {Q : ℕ} (hQ : 0 < Q) :
    ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, V t)+Δ n*x):UnitAddCircle)) ∧
      ∃ C Cq : ι → ℝ, (∀ i, 0 ≤ C i) ∧ (∀ i, 0 ≤ Cq i) ∧ ∀ L : ℝ, 0 < L → ∀ β : ℝ,
        let ψ := neutralCircleCutoff c
        let J := neutralJitter c L β
        let J₀ := neutralJitterReal c L β
        let σ := fun (n : ℕ) a => (((1+J a/n)/n:ℝ):UnitAddCircle)
        (∀ n, Smooth (torusPassage (H n) (σ n)) ∧
          Smooth (torusPassage (H n) (σ n)).symm ∧
          MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
        (∀ n, 0 < n → ∀ x : Cover,
          torusPassage (H n) (σ n) (project x) =
            project (passageFamily V J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
          (torusPassage (H n) (σ n)).symm (project x) =
            project (passageFamily V J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
        (∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ d : ℕ,
          TendstoUniformlyOn
            (fun (n : ℕ) x => iteratedFDeriv ℝ d (passageFamily V J₀ r ((n:ℝ)⁻¹,Δ n)) x)
            (fun x => iteratedFDeriv ℝ d (fun y : Cover => ![y 0+r*V (y 1),y 1,y 2]) x)
            atTop K) ∧
        ∃ S : ℕ → ι → Finset ℤ,
          (∀ n, 0 < n → ∀ i j, j ∈ S n i → j ≠ 0) ∧
          (∀ n, 0 < n → ∀ i j, j ∉ S n i → ∀ a, χ i ((j:ℝ)/n) a = 0) ∧
          (∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0) ∧
          ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
            0 < n ∧ ∀ i,
            let f := retainedPassage (m i) (H n) (A i) (S n i) (fun j => χ i ((j:ℝ)/n)) ψ
            let p := exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ (χ i) (m i) H (A i) (S n i) n
            let pold := foldCircleDensity (fun s => ∫ a, stationaryWeight (Icc (l-R) (u+R))
              (fun x => (m i:ℝ)*V x) (A₀ i a) s ∂AddCircle.haarAddCircle)
            (∫ x : TripleTorus, ‖packet (m i) (A i) x-f (passageChart (H n) x)‖^2 ∂tripleVolume) <
              8*δ*B i+η ∧
            (∫ z, |p z-pold z| ∂AddCircle.haarAddCircle) < C i/L+4*δ*B i+η ∧
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p x) ∧
            (∀ k : ℤ, (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter (σ n) k x) ∂tripleVolume) =
              ∫ z, (p z:ℂ)*fourier k z ∂AddCircle.haarAddCircle) ∧
            (∀ j u a, ‖retainedAmplitude ψ (χ i) (m i) H (A i) n j (u,a)‖ =
              ‖retainedAmplitude ψ (χ i) (m i) H (A i) n j (u,0)‖) ∧
            (∑ h : Fin Q, ∫ z,
              |exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ (χ i) (m i) H (A i)
                ((S n i).filter (fun j => j % (Q:ℤ) = (h.val:ℤ) % (Q:ℤ))) n z-
                (Q:ℝ)⁻¹*pold z| ∂AddCircle.haarAddCircle) < Cq i/L+4*δ*B i+η := by
  classical
  obtain ⟨Δ,H,hΔ,hΔt,hHc,hHe,hgeo⟩ := exists_rounded_primitive_family hp hV
  have hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∫ t in 0..x, V t) :=
    contDiff_real_primitive hV
  have hPV : deriv (fun x => ∫ t in 0..x, V t) = V := deriv_real_primitive hV.continuous
  have hv : Continuous hp.lift := by
    apply Continuous.quotient_lift
    exact hV.continuous
  have heV (x : ℝ) : hp.lift (x:UnitAddCircle) = V x := rfl
  have hneutral i := exact_neutral_passage (hm i) hHe (hA i) (hA₀ i) (hAc i) (hAd i)
    (hAr i) (hsupp i) hlo huo hlu hR hPr hV hPV hdV (h0 i) hHc (hAcont i) hΔt (hAs i)
    hv.measurable heV (hB i) (hAb i) c hδ hδ' (hχs i) (hχc i) (hcχ i) (hzχ i) (hχ i) (hχW i)
  choose C hC hrest using hneutral
  have hresidue i := exact_neutral_residue_refresh (hm i) hHe (hA i) (hA₀ i) (hAc i) (hAd i)
    (hAr i) (hsupp i) hlo huo hlu hR hPr hV hPV hdV (h0 i) hHc (hAcont i) hΔt
    hv.measurable heV (hB i) (hAb i) c hδ hδ' (hχc i) (hcχ i) (hzχ i) (hχ i) (hχW i) hQ
  choose Cq hCq hres using hresidue
  refine ⟨Δ,H,hΔ,hΔt,hHc,hHe,C,Cq,hC,hCq,?_⟩
  intro L hL β
  dsimp only
  obtain ⟨hg,hgraph,hlimit⟩ := hgeo (neutralJitterReal c L β)
    (neutralJitterReal_periodic c L β) (neutralJitterReal_smooth c L β)
  refine ⟨hg,hgraph,hlimit,?_⟩
  choose S hSN hST hgood using fun i => hrest i L hL β
  obtain ⟨T,hTN,hTE⟩ := cylinder_cutoff_exact_indices χ hcχ hzχ
  have hTZ n (hn : 0 < n) i j (hj : j ∉ T n i) a : χ i ((j:ℝ)/n) a = 0 := by
    by_contra hh
    exact hj ((hTE n hn i j).mpr ⟨a,hh⟩)
  refine ⟨T,fun n _ i => hTN n i,hTZ,hTE,?_⟩
  intro η hη
  have hgall := (Filter.eventually_all).mpr (fun i => hgood i η hη)
  have hqall := (Filter.eventually_all).mpr (fun i => hres i L hL β (fun n => T n i)
    (fun n _ => hTN n i) (fun n hn => hTZ n hn i) η hη)
  filter_upwards [eventually_gt_atTop (0:ℕ),hgall,hqall] with n hn hall hq
  refine ⟨hn,fun i => ?_⟩
  have ef := retainedPassage_eq_of_cover (m i) (H n) (A i) (S i n) (T n i)
    (fun j => χ i ((j:ℝ)/n)) (neutralCircleCutoff c) (hST i n hn) (hTZ n hn i)
  have ep := exactRetainedPacketDensity_eq_of_cover (Ioo δ (1-δ))
    (neutralJitterReal c L β) (neutralCircleCutoff c) (χ i) (m i) H (A i)
    (S i n) (T n i) n (hST i n hn) (hTZ n hn i)
  have hh := hall i
  dsimp only at hh
  rw [ef,ep] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hq i⟩

end ThreeTorus
end
end

section

/-! An unconditional neutral refresh on the concrete iterable packet class.
All cutoffs, carrier, broad jitter and rounded geometry are constructed, in
that order. The new state uses the literal coefficients and its canonical
spectra, not abstract model arrays. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- Full neutral state producer. Both approximation errors may be arbitrarily
small. The same output state has all actual spectral moments, exactly disjoint
angular indices, and the residue refresh statement. -/
theorem eventually_neutral_state_family {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) (hi : Injective F.m) (hmod : F.SpareIndependent)
    {Q : ℕ} (hQ : 0 < Q) {ε τ : ℝ} (hε : 0 < ε) (hτ : 0 < τ) :
    ∀ᶠ c : ℕ in atTop, 0 < c ∧ ∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ L : ℝ,
      ∃ χ : ι → ℝ → ℝ, ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      0 < δ ∧ δ < 1/8 ∧ 0 < L ∧
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
              fun z => ∑ j : ↥(S n i), if E j.val then G.density ⟨i,j⟩ z else 0) := by
  classical
  obtain ⟨B,hB,hAB⟩ := F.amplitude_bound
  have hden : 0 < 32*(B+1) := by positivity
  obtain ⟨δ,hδ,hδhi⟩ := exists_between (lt_min (by norm_num : (0:ℝ)<1/8) (div_pos hε hden))
  have hδ' : δ < 1/8 := hδhi.trans_le (min_le_left _ _)
  have hδB : 8*δ*B < ε/4 := by
    have hh := (lt_div_iff₀ hden).mp (hδhi.trans_le (min_le_right _ _))
    nlinarith
  let cut := lawCutoffs δ hδ hδ'
  filter_upwards [F.tracked_cutoffs hi hmod hτ,
    eventually_integral_speed_separation F.m F.periodic.lift F.nonzero F.speed_continuous] with c hc hsep
  obtain ⟨hcp,χ,hχ,hdisj⟩ := hc
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
  refine ⟨hcp,δ,cut,L,χ,Δ,H,hδ,hδ',hL,?_,hdisj,hΔ,hΔt,hHc,?_,?_,?_,?_,S,hSd,hTE',?_⟩
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
    obtain ⟨G,hGm,hGA,_hGA₀,hGV,_hGo,_hGl,_hGu,hGmod⟩ := literal_output_packets
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
    refine ⟨G,?_,hGmod,hGV,hGm,hGA,hGden,?_⟩
    · have he : G.m = fun i : PassageOutputIndex (S n) => i.2.val := funext hGm
      rw [he]
      exact output_index_injective (hSd n hn0)
    · intro i E inst
      simp_rw [hGden]
      exact exactRetainedPacketDensity_filtered_singletons hJs isOpen_Ioo hJinj
        (fun x hx => (hJd x hx).ne') cut.ψ_smooth cut.ψ_compact heψ hsψ (hXs i)
        hHl hHe (F.smooth_amplitude i) hn0 (hSN n hn0 i) E

end ThreeTorus
end
end

section

/-! The anchor carrier can be fixed BEFORE all accuracy parameters and the
signal law. The source's order of choices is implemented literally. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

lemma tracked_cutoffs_fixed_carrier {ι : Type*} [Finite ι]
    (F : PassagePackets ι) (hi : Injective F.m) (hmod : F.SpareIndependent)
    {c : ℕ}
    (hc : 0 < c ∧ (∀ i x, (F.m i:ℝ)*((c:ℝ)+F.periodic.lift x) ≠ 0) ∧
      ∀ i j x y, (F.m i:ℝ)*((c:ℝ)+F.periodic.lift x) =
        (F.m j:ℝ)*((c:ℝ)+F.periodic.lift y) → F.m i = F.m j)
    {η : ℝ} (hη : 0 < η) :
    0 < c ∧ ∃ χ : ι → ℝ → ℝ,
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        χ i 0 = 0 ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        (∀ s ∈ tsupport (χ i), ∃ x ∈ F.core i, |s-(F.m i:ℝ)*((c:ℝ)+F.V x)| < η) ∧
        ∀ (C : Set ℝ) a s, stationaryWeight C
          (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i a) s ≠ 0 → χ i s = 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) := by
  have hzero i : 0 ∉ (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) '' F.core i := by
    rintro ⟨x,_hx,he⟩
    exact hc.2.1 i (x:UnitAddCircle) he
  have hsep : Pairwise (fun i j => Disjoint
      ((fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) '' F.core i)
      ((fun x => (F.m j:ℝ)*((c:ℝ)+F.V x)) '' F.core j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro s ⟨x,_hx,rfl⟩ ⟨y,_hy,he⟩
    exact hij (hi (hc.2.2 i j (x:UnitAddCircle) (y:UnitAddCircle) he.symm))
  obtain ⟨χ,hχ,hd⟩ := tracked_frequency_cutoffs F.m (fun x => (c:ℝ)+F.V x) F.core
    (continuous_const.add F.smooth_speed.continuous) F.core_compact hzero hsep hη
  exact ⟨hc.1,χ,fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1,
    (hχ i).2.2.2.1,(hχ i).2.2.2.2.2.1,fun C a s =>
      (hχ i).2.2.2.2.2.2 C (F.A₀ i a) (F.support_subset_core hmod i a) s⟩,hd⟩

theorem eventually_neutral_anchor_family {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) (hi : Injective F.m) (hmod : F.SpareIndependent)
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
              fun z => ∑ j : ↥(S n i), if E j.val then G.density ⟨i,j⟩ z else 0) := by
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
  obtain ⟨hcp,χ,hχ,hdisj⟩ := tracked_cutoffs_fixed_carrier F hi hmod hsep hτ
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
    obtain ⟨G,hGm,hGA,_hGA₀,hGV,_hGo,_hGl,_hGu,hGmod⟩ := literal_output_packets
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
    refine ⟨G,?_,hGmod,hGV,hGm,hGA,hGden,?_⟩
    · have he : G.m = fun i : PassageOutputIndex (S n) => i.2.val := funext hGm
      rw [he]
      exact output_index_injective (hSd n hn0)
    · intro i E inst
      simp_rw [hGden]
      exact exactRetainedPacketDensity_filtered_singletons hJs isOpen_Ioo hJinj
        (fun x hx => (hJd x hx).ne') cut.ψ_smooth cut.ψ_compact heψ hsψ (hXs i)
        hHl hHe (F.smooth_amplitude i) hn0 (hSN n hn0 i) E

end ThreeTorus
end
end

section

/-! Conjugation symmetry survives the literal retained coefficients. Smooth
cutoffs can be made reflection-compatible by a product, without losing the
already constructed exact disjointness of their supports. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

def pairedCylinderCutoff {ι : Type*} (τ : ι → ι)
    (χ : ι → ℝ → UnitAddCircle → ℝ) (i : ι) (s : ℝ) (a : UnitAddCircle) : ℝ :=
  χ i s a * χ (τ i) (-s) a

lemma pairedCylinderCutoff_reflect {ι : Type*} {τ : ι → ι}
    (hτ : Involutive τ) (χ : ι → ℝ → UnitAddCircle → ℝ) (i : ι) (s : ℝ) (a : UnitAddCircle) :
    pairedCylinderCutoff τ χ (τ i) s a = pairedCylinderCutoff τ χ i (-s) a := by
  simp only [pairedCylinderCutoff,hτ i,neg_neg,mul_comm]

lemma pairedCylinderCutoff_smooth {ι : Type*} (τ : ι → ι)
    {χ : ι → ℝ → UnitAddCircle → ℝ} (hχ : ∀ i, CylinderSmooth (χ i).uncurry) (i : ι) :
    CylinderSmooth (pairedCylinderCutoff τ χ i).uncurry := by
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun p : ℝ × ℝ => χ i p.1 (p.2:UnitAddCircle) * χ (τ i) (-p.1) (p.2:UnitAddCircle))
  exact (hχ i).mul ((hχ (τ i)).comp (contDiff_fst.neg.prodMk contDiff_snd))

lemma pairedCylinderCutoff_tsupport {ι : Type*} (τ : ι → ι)
    (χ : ι → ℝ → UnitAddCircle → ℝ) (i : ι) :
    tsupport (pairedCylinderCutoff τ χ i).uncurry ⊆ tsupport (χ i).uncurry :=
  tsupport_mul_subset_left

lemma pairedCylinderCutoff_compact {ι : Type*} (τ : ι → ι)
    {χ : ι → ℝ → UnitAddCircle → ℝ} (hχ : ∀ i, HasCompactSupport (χ i).uncurry) (i : ι) :
    HasCompactSupport (pairedCylinderCutoff τ χ i).uncurry :=
  (hχ i).mul_right

lemma pairedCylinderCutoff_disjoint {ι : Type*} (τ : ι → ι)
    {χ : ι → ℝ → UnitAddCircle → ℝ}
    (hd : Pairwise (fun i j => Disjoint (tsupport (χ i).uncurry) (tsupport (χ j).uncurry))) :
    Pairwise (fun i j => Disjoint (tsupport (pairedCylinderCutoff τ χ i).uncurry)
      (tsupport (pairedCylinderCutoff τ χ j).uncurry)) := by
  intro i j hij
  exact (hd hij).mono (pairedCylinderCutoff_tsupport τ χ i) (pairedCylinderCutoff_tsupport τ χ j)

lemma pairedCylinderCutoff_bounds {ι : Type*} (τ : ι → ι)
    {χ : ι → ℝ → UnitAddCircle → ℝ} (hχ : ∀ i s a, 0 ≤ χ i s a ∧ χ i s a ≤ 1)
    (i : ι) (s : ℝ) (a : UnitAddCircle) :
    0 ≤ pairedCylinderCutoff τ χ i s a ∧ pairedCylinderCutoff τ χ i s a ≤ 1 := by
  refine ⟨mul_nonneg (hχ i s a).1 (hχ (τ i) (-s) a).1,?_⟩
  exact (mul_le_mul (hχ i s a).2 (hχ (τ i) (-s) a).2 (hχ (τ i) (-s) a).1 zero_le_one).trans
    (by norm_num)

lemma pairedCylinderCutoff_one {ι : Type*} (τ : ι → ι)
    {χ : ι → ℝ → UnitAddCircle → ℝ} {K : ι → Set (ℝ × UnitAddCircle)}
    (hK : ∀ i p, p ∈ K i → (-p.1,p.2) ∈ K (τ i))
    (hχ : ∀ i p, p ∈ K i → (χ i).uncurry =ᶠ[𝓝 p] 1)
    (i : ι) (p : ℝ × UnitAddCircle) (hp : p ∈ K i) :
    (pairedCylinderCutoff τ χ i).uncurry =ᶠ[𝓝 p] 1 := by
  have he₁ := hχ i p hp
  have he₂ := (hχ (τ i) (-p.1,p.2) (hK i p hp)).comp_tendsto
    ((continuous_fst.neg.prodMk continuous_snd).tendsto p)
  filter_upwards [he₁,he₂] with q hq₁ hq₂
  change χ i q.1 q.2 * χ (τ i) (-q.1) q.2 = 1
  change χ i q.1 q.2 = 1 at hq₁
  change χ (τ i) (-q.1) q.2 = 1 at hq₂
  rw [hq₁,hq₂,one_mul]

lemma symmetric_exact_indices {ι : Type*} {τ : ι → ι}
    {χ : ι → ℝ → UnitAddCircle → ℝ}
    (hc : ∀ i, HasCompactSupport (χ i).uncurry) (hz : ∀ i a, χ i 0 a = 0)
    (hsym : ∀ i s a, χ (τ i) s a = χ i (-s) a) :
    ∃ S : ℕ → ι → Finset ℤ,
      (∀ n i j, j ∈ S n i → j ≠ 0) ∧
      (∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0) ∧
      ∀ n, 0 < n → ∀ i j, j ∈ S n (τ i) ↔ -j ∈ S n i := by
  obtain ⟨S,hS0,hS⟩ := cylinder_cutoff_exact_indices χ hc hz
  refine ⟨S,hS0,hS,?_⟩
  intro n hn i j
  rw [hS n hn (τ i) j,hS n hn i (-j)]
  simp only [hsym,Int.cast_neg,neg_div]

lemma retainedAmplitude_reflect (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) (p : UnitAddCircle × UnitAddCircle) :
    retainedAmplitude ψ (fun s a => χ (-s) a) (-m) H (fun x => conj (A x)) n j p =
      conj (retainedAmplitude ψ χ m H A n (-j) p) := by
  simp only [retainedAmplitude,exactPassageCoeff_neg,Int.cast_neg,neg_div,map_mul,
    Complex.conj_ofReal,fourier_neg]

lemma packet_reflect (m : ℤ) (A : UnitAddCircle × UnitAddCircle → ℂ) (x : TripleTorus) :
    packet (-m) (fun p => conj (A p)) x = conj (packet m A x) := by
  simp only [packet,map_mul,fourier_neg]

lemma retainedPassage_reflect (ψ : UnitAddCircle → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S : Finset ℤ) (n : ℕ) (x : TripleTorus) :
    retainedPassage (-m) (H n) (fun p => conj (A p)) (S.image Neg.neg)
      (fun j a => χ (-(j:ℝ)/n) a) ψ x =
      conj (retainedPassage m (H n) A S (fun j => χ ((j:ℝ)/n)) ψ x) := by
  classical
  have he : (fun (j : ℤ) a => χ (-(j:ℝ)/n) a) =
      (fun (j : ℤ) a => (fun s a => χ (-s) a) ((j:ℝ)/n) a) := by
    funext j a
    rw [neg_div]
  rw [he]
  change (∑ j ∈ S.image Neg.neg,
    packet j (retainedAmplitude ψ (fun s a => χ (-s) a) (-m) H
      (fun p => conj (A p)) n j) x) =
        conj (∑ j ∈ S, packet j (retainedAmplitude ψ χ m H A n j) x)
  rw [Finset.sum_image (fun _ _ _ _ h => neg_injective h),map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  have ha : retainedAmplitude ψ (fun s a => χ (-s) a) (-m) H (fun p => conj (A p)) n (-j) =
      fun p => conj (retainedAmplitude ψ χ m H A n j p) := by
    funext p
    simpa only [neg_neg] using retainedAmplitude_reflect ψ χ m H A n (-j) p
  rw [ha,packet_reflect]

end ThreeTorus
end
end

section

/-! Actual conjugation data, invariant cutoff choices, and canonical spectral
reflection. No symmetry of an approximate model is substituted for reality of
the packets. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

/-- The entire increasing good arc, including its relation to the lifted
support interval. The excluded length is exactly `2*δ`. -/
def GoodArc (δ : ℝ) : Prop :=
  F.o = 0 ∧ δ < F.l ∧ F.u < 1-δ ∧
    ∀ x ∈ Ioo δ (1-δ), 0 < deriv F.V x

structure Reflection (τ : ι → ι) : Prop where
  index : ∀ i, F.m (τ i) = -F.m i
  amplitude : ∀ i p, F.A (τ i) p = conj (F.A i p)
  lift : ∀ i a x, F.A₀ (τ i) a x = conj (F.A₀ i a x)

variable {F}

lemma Reflection.involutive {τ : ι → ι} (h : F.Reflection τ) (hi : Injective F.m) :
    Involutive τ := fun i => hi (by rw [h.index,h.index,neg_neg])

lemma Reflection.core {τ : ι → ι} (h : F.Reflection τ) (i : ι) :
    F.core (τ i) = F.core i := by
  unfold PassagePackets.core tsupport
  congr 1
  ext x
  simp only [mem_support,h.lift,map_ne_zero]

lemma Reflection.weight {τ : ι → ι} (h : F.Reflection τ) (i : ι) (s : ℝ) :
    F.weight (τ i) s = F.weight i (-s) := by
  have hinj := (scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv).1
  have ha : F.A₀ (τ i) 0 = fun x => conj (F.A₀ i 0 x) := funext (h.lift i 0)
  simp only [PassagePackets.weight,h.index,ha,Int.cast_neg,neg_mul]
  exact stationaryWeight_reflect hinj _ s

end PassagePackets

lemma foldCircleDensity_reflect (q : ℝ → ℝ) (z : UnitAddCircle) :
    foldCircleDensity (fun s => q (-s)) z = foldCircleDensity q (-z) := by
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective z
  rw [← AddCircle.coe_neg,foldCircleDensity_coe_all,foldCircleDensity_coe_all]
  calc
    (∑' k : ℤ, q (-(x+k))) = ∑' k : ℤ, q (-x+(-k:ℤ)) := by
      apply tsum_congr
      intro k
      congr 1
      simp only [Int.cast_neg]
      ring
    _ = ∑' k : ℤ, q (-x+k) := (Equiv.neg ℤ).tsum_eq (fun k => q (-x+k))

lemma PassagePackets.Reflection.density {ι : Type*} {F : PassagePackets ι}
    {τ : ι → ι} (h : F.Reflection τ) (i : ι) (z : UnitAddCircle) :
    F.density (τ i) z = F.density i (-z) := by
  unfold PassagePackets.density
  rw [show F.weight (τ i) = (fun s => F.weight i (-s)) from funext (h.weight i)]
  exact foldCircleDensity_reflect _ z

/-- Reflection-compatible, exactly disjoint cutoffs with the full tracking
and stationary identity used by the actual neutral and signal producers. -/
theorem tracked_symmetric_cutoffs_fixed_carrier {ι : Type*} [Finite ι]
    (F : PassagePackets ι) (hi : Injective F.m) (hmod : F.SpareIndependent)
    {τ : ι → ι} (hr : F.Reflection τ) {c : ℕ}
    (hc : 0 < c ∧ (∀ i x, (F.m i:ℝ)*((c:ℝ)+F.periodic.lift x) ≠ 0) ∧
      ∀ i j x y, (F.m i:ℝ)*((c:ℝ)+F.periodic.lift x) =
        (F.m j:ℝ)*((c:ℝ)+F.periodic.lift y) → F.m i = F.m j)
    {η : ℝ} (hη : 0 < η) :
    0 < c ∧ ∃ χ : ι → ℝ → ℝ,
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        χ i 0 = 0 ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        (∀ s ∈ tsupport (χ i), ∃ x ∈ F.core i, |s-(F.m i:ℝ)*((c:ℝ)+F.V x)| < η) ∧
        ∀ (C : Set ℝ) a s, stationaryWeight C
          (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i a) s ≠ 0 → χ i s = 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
      (∀ i s, χ (τ i) s = χ i (-s)) := by
  have hzero i : 0 ∉ (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) '' F.core i := by
    rintro ⟨x,_hx,he⟩
    exact hc.2.1 i (x:UnitAddCircle) he
  have hsep : Pairwise (fun i j => Disjoint
      ((fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) '' F.core i)
      ((fun x => (F.m j:ℝ)*((c:ℝ)+F.V x)) '' F.core j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro s ⟨x,_hx,rfl⟩ ⟨y,_hy,he⟩
    exact hij (hi (hc.2.2 i j (x:UnitAddCircle) (y:UnitAddCircle) he.symm))
  obtain ⟨χ,hχ,hd⟩ := tracked_frequency_cutoffs F.m (fun x => (c:ℝ)+F.V x) F.core
    (continuous_const.add F.smooth_speed.continuous) F.core_compact hzero hsep hη
  let ψ : ι → ℝ → ℝ := fun i s => χ i s*χ (τ i) (-s)
  have hsub i : tsupport (ψ i) ⊆ tsupport (χ i) := tsupport_mul_subset_left
  refine ⟨hc.1,ψ,fun i => ⟨(hχ i).1.mul ((hχ (τ i)).1.comp contDiff_neg),
    (hχ i).2.1.mul_right,?_,?_,?_,?_⟩,?_,?_⟩
  · simp only [ψ,(hχ i).2.2.1,zero_mul]
  · intro s
    exact ⟨mul_nonneg ((hχ i).2.2.2.1 s).1 ((hχ (τ i)).2.2.2.1 (-s)).1,
      (mul_le_mul ((hχ i).2.2.2.1 s).2 ((hχ (τ i)).2.2.2.1 (-s)).2
        ((hχ (τ i)).2.2.2.1 (-s)).1 zero_le_one).trans (by norm_num)⟩
  · intro s hs
    exact (hχ i).2.2.2.2.2.1 s (hsub i hs)
  · intro C a s hs
    have hsi := stationaryWeight_support_subset (F.support_subset_core hmod i a) hs
    obtain ⟨x,hx,hxs⟩ := hsi
    have hre : -s ∈ (fun x => (F.m (τ i):ℝ)*((c:ℝ)+F.V x)) '' F.core (τ i) := by
      refine ⟨x,(hr.core i).symm ▸ hx,?_⟩
      simp only [hr.index,Int.cast_neg,neg_mul,hxs]
    have hleft := (hχ i).2.2.2.2.2.2 C (F.A₀ i a) (F.support_subset_core hmod i a) s hs
    have hright := ((hχ (τ i)).2.2.2.2.1 (-s) hre).self_of_nhds
    change χ (τ i) (-s) = 1 at hright
    simp only [ψ,hleft,hright,one_mul]
  · intro i j hij
    exact (hd hij).mono (hsub i) (hsub j)
  · intro i s
    simp only [ψ,hr.involutive hi i,neg_neg,mul_comm]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets
variable {ι κ : Type*} (F : PassagePackets ι)

def cylinderCore (i : ι) : Set (ℝ × UnitAddCircle) :=
  tsupport (fun p : ℝ × UnitAddCircle => F.A₀ i p.2 p.1)

lemma cylinderCore_subset (i : ι) : F.cylinderCore i ⊆ Icc F.l F.u ×ˢ univ := by
  apply closure_minimal
  · intro p hp
    exact ⟨⟨(F.support_lift i p.2 hp).1.le,(F.support_lift i p.2 hp).2⟩,mem_univ _⟩
  · exact isClosed_Icc.prod isClosed_univ

lemma cylinderCore_compact (i : ι) : IsCompact (F.cylinderCore i) :=
  (isCompact_Icc.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport _) (F.cylinderCore_subset i)

lemma support_subset_cylinderCore (i : ι) (a : UnitAddCircle) {x : ℝ}
    (hx : x ∈ support (F.A₀ i a)) : (x,a) ∈ F.cylinderCore i := subset_tsupport _ hx

lemma reflection_cylinderCore {τ : ι → ι} (hr : F.Reflection τ) (i : ι) :
    F.cylinderCore (τ i) = F.cylinderCore i := by
  unfold cylinderCore tsupport
  congr 1
  ext p
  simp only [mem_support,hr.lift,map_ne_zero]

/-- Multiply the literal torus amplitudes by smooth disjoint cylinder
cutoffs and retain their actual lifts. All passage regularity is derived. -/
def clipped (q : κ → ι) (χ : κ → ℝ × UnitAddCircle → ℝ)
    (hχ : ∀ k, CylinderSmooth (χ k)) (hc : ∀ k, HasCompactSupport (χ k))
    (hs : ∀ k, support (χ k) ⊆ Ioo F.o (F.o+1) ×ˢ univ) : PassagePackets κ where
  m := fun k => F.m (q k)
  nonzero := fun k => F.nonzero (q k)
  A := fun k p => (cylinderTorusCutoff (χ k) p:ℂ)*F.A (q k) p
  A₀ := fun k a x => (χ k (x,a):ℂ)*F.A₀ (q k) a x
  o := F.o
  l := F.l
  u := F.u
  R := F.R
  lo := F.lo
  uo := F.uo
  lu := F.lu
  Rpos := F.Rpos
  lift_matches := by
    intro k a x hx
    rw [cylinderTorusCutoff_eq (hs k) hx,F.lift_matches (q k) a x hx]
  two := by
    intro k a
    have hh := (cylinder_smooth_regular (hχ k)).1 a
    exact ((Complex.ofRealCLM.contDiff.comp hh).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2:ℕ∞) ≤ ⊤))).mul (F.two (q k) a)
  continuous_lift := by
    intro k
    exact (Complex.continuous_ofReal.comp ((hχ k).continuous.comp continuous_swap)).mul
      (F.continuous_lift (q k))
  continuous_deriv := by
    intro k
    have he (p : UnitAddCircle × ℝ) :
        deriv (fun x => (χ k (x,p.1):ℂ)*F.A₀ (q k) p.1 x) p.2 =
          Complex.ofReal (deriv (fun x => χ k (x,p.1)) p.2)*F.A₀ (q k) p.1 p.2 +
          (χ k (p.2,p.1):ℂ)*deriv (F.A₀ (q k) p.1) p.2 := by
      have hχd := ((cylinder_smooth_regular (hχ k)).1 p.1).differentiable (by simp) p.2
      have hFd := (F.two (q k) p.1).differentiable (by norm_num) p.2
      have hx : HasDerivAt (fun x => (χ k (x,p.1):ℂ))
          (Complex.ofReal (deriv (fun x => χ k (x,p.1)) p.2)) p.2 :=
        Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt _ hχd.hasDerivAt
      exact (hx.mul hFd.hasDerivAt).deriv
    simp_rw [he]
    exact ((Complex.continuous_ofReal.comp ((cylinder_smooth_regular (hχ k)).2.2.comp continuous_swap)).mul
      (F.continuous_lift (q k))).add
      ((Complex.continuous_ofReal.comp ((hχ k).continuous.comp continuous_swap)).mul (F.continuous_deriv (q k)))
  smooth_lift := fun k => (Complex.ofRealCLM.contDiff.comp (hχ k)).mul (F.smooth_lift (q k))
  support_lift := by
    intro k a x hx
    apply F.support_lift (q k) a
    intro hz
    exact hx (by simp [hz])
  continuous_amplitude := fun k => (Complex.continuous_ofReal.comp
    (cylinderTorusCutoff_continuous (hχ k) (hc k))).mul (F.continuous_amplitude (q k))
  smooth_amplitude := fun k => (Complex.ofRealCLM.contDiff.comp
    (cylinderTorusCutoff_smooth (hχ k) (hc k))).mul (F.smooth_amplitude (q k))
  V := F.V
  periodic := F.periodic
  smooth_speed := F.smooth_speed
  positive_deriv := F.positive_deriv

lemma clipped_core_subset (q : κ → ι) (χ : κ → ℝ × UnitAddCircle → ℝ)
    (hχ : ∀ k, CylinderSmooth (χ k)) (hc : ∀ k, HasCompactSupport (χ k))
    (hs : ∀ k, support (χ k) ⊆ Ioo F.o (F.o+1) ×ˢ univ) (k : κ) :
    (F.clipped q χ hχ hc hs).cylinderCore k ⊆ tsupport (χ k) := by
  apply closure_minimal
  · intro p hp
    apply subset_tsupport
    intro hz
    exact hp (by simp [clipped,hz])
  · exact isClosed_tsupport _

end PassagePackets
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- First of the two neutral separations: equal angular modes are separated
using the ACTUAL two-dimensional compact coefficient supports. In particular
no spare-independence or injectivity of the old mode list is assumed. -/
theorem first_separation_cutoffs {ι : Type*} [Finite ι]
    (F : PassagePackets ι)
    (hd : ∀ i j, i ≠ j → F.m i = F.m j → Disjoint (F.cylinderCore i) (F.cylinderCore j))
    (τ : ι → ι) (hτ : Involutive τ) (hr : F.Reflection τ) :
    ∃ c : ℕ, 0 < c ∧ (∀ x : ℝ, (c:ℝ)+F.V x ≠ 0) ∧
      ∃ χ : ι → ℝ → UnitAddCircle → ℝ,
        (∀ i, CylinderSmooth (χ i).uncurry ∧ HasCompactSupport (χ i).uncurry ∧
          (∀ a, χ i 0 a = 0) ∧ (∀ s a, 0 ≤ χ i s a ∧ χ i s a ≤ 1) ∧
          ∀ (C : Set ℝ) a s, stationaryWeight C
            (fun x => (F.m i:ℝ)*((c:ℝ)+F.V x)) (F.A₀ i a) s ≠ 0 → χ i s a = 1) ∧
        Pairwise (fun i j => Disjoint (tsupport (χ i).uncurry) (tsupport (χ j).uncurry)) ∧
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
  have hi : InjOn V (Icc F.l F.u) := by
    apply StrictMonoOn.injOn
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hV.continuousOn
    intro x hx
    have hx' := interior_subset hx
    dsimp [V]
    rw [deriv_const_add]
    exact F.positive_deriv x ⟨by linarith [hx'.1,F.Rpos],by linarith [hx'.2,F.Rpos]⟩
  let E (i : ι) := stationaryImage (F.m i) V (F.cylinderCore i)
  have hEc i : IsCompact (E i) := stationaryImage_compact hV (F.cylinderCore_compact i)
  have hEd : Pairwise (Disjoint on E) := by
    intro i j hij
    by_cases he : F.m i = F.m j
    · change Disjoint (stationaryImage (F.m i) V (F.cylinderCore i))
        (stationaryImage (F.m j) V (F.cylinderCore j))
      rw [← he]
      exact stationaryImage_disjoint_same (F.nonzero i) hi
        (F.cylinderCore_subset i) (F.cylinderCore_subset j) (hd i j hij he)
    · apply stationaryImage_disjoint_distinct
      intro p hp q hq h
      exact he (hsep (some i) (some j) (p.1:UnitAddCircle) (q.1:UnitAddCircle) h)
  let U : Set (ℝ × UnitAddCircle) := {p | p.1 ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun continuous_fst continuous_const
  have hEU i : E i ⊆ U := by
    rintro _ ⟨p,hp,rfl⟩
    exact mul_ne_zero (by exact_mod_cast F.nonzero i) (h0 p.1)
  obtain ⟨ξ,hξ,hξd⟩ := finite_disjoint_cylinder_cutoffs E (fun _ => U) hEc (fun _ => hU) hEU hEd
  let χ : ι → ℝ → UnitAddCircle → ℝ := fun i s a => ξ i (s,a)*ξ (τ i) (-s,a)
  have hsub i : tsupport (χ i).uncurry ⊆ tsupport (ξ i) := tsupport_mul_subset_left
  have hre i {s : ℝ} {a : UnitAddCircle} (hs : (s,a) ∈ E i) : (-s,a) ∈ E (τ i) := by
    obtain ⟨p,hp,he⟩ := hs
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    dsimp only at he1 he2
    refine ⟨p,(F.reflection_cylinderCore hr i).symm ▸ hp,?_⟩
    apply Prod.ext
    · change (F.m (τ i):ℝ)*V p.1 = -s
      rw [hr.index,Int.cast_neg,neg_mul,he1]
    · exact he2
  have hsE (i : ι) (C : Set ℝ) (a : UnitAddCircle) (s : ℝ)
      (hs : stationaryWeight C (fun x => (F.m i:ℝ)*V x) (F.A₀ i a) s ≠ 0) :
      (s,a) ∈ E i := by
    obtain ⟨x,hx,hxs⟩ := stationaryWeight_support_subset
      (show support (F.A₀ i a) ⊆ {x | (x,a) ∈ F.cylinderCore i} from
        fun x hx => F.support_subset_cylinderCore i a hx) hs
    exact ⟨(x,a),hx,Prod.ext hxs rfl⟩
  refine ⟨c,hc,h0,χ,fun i => ⟨?_,?_,?_,?_,?_⟩,?_,?_⟩
  · exact (hξ i).1.mul ((hξ (τ i)).1.comp (contDiff_fst.neg.prodMk contDiff_snd))
  · exact (hξ i).2.1.mul_right
  · intro a
    have hz : ξ i (0,a) = 0 := by
      by_contra hh
      exact (hξ i).2.2.1 (subset_tsupport _ hh) rfl
    simp [χ,hz]
  · intro s a
    exact ⟨mul_nonneg ((hξ i).2.2.2.1 (s,a)).1 ((hξ (τ i)).2.2.2.1 (-s,a)).1,
      (mul_le_mul ((hξ i).2.2.2.1 (s,a)).2 ((hξ (τ i)).2.2.2.1 (-s,a)).2
        ((hξ (τ i)).2.2.2.1 (-s,a)).1 zero_le_one).trans (by norm_num)⟩
  · intro C a s hs
    have hs' := hsE i C a s hs
    have h1 := ((hξ i).2.2.2.2 (s,a) hs').self_of_nhds
    have h2 := ((hξ (τ i)).2.2.2.2 (-s,a) (hre i hs')).self_of_nhds
    change ξ i (s,a) = 1 at h1
    change ξ (τ i) (-s,a) = 1 at h2
    simp only [χ,h1,h2,one_mul]
  · intro i j hij
    exact (hξd hij).mono (hsub i) (hsub j)
  · intro i s a
    simp only [χ,hτ i,neg_neg,mul_comm]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

def marginalWeight (i : ι) (s : ℝ) : ℝ :=
  ∫ a, stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
    (fun x => (F.m i:ℝ)*F.V x) (F.A₀ i a) s ∂AddCircle.haarAddCircle

def marginalDensity (i : ι) : UnitAddCircle → ℝ := foldCircleDensity (F.marginalWeight i)

lemma marginalWeight_regular (i : ι) : Continuous (F.marginalWeight i) ∧
    HasCompactSupport (F.marginalWeight i) := by
  let w : ℝ × UnitAddCircle → ℝ := fun p => stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
    (fun x => (F.m i:ℝ)*F.V x) (F.A₀ i p.2) p.1
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have hw := stationaryWeight_signed_compact_continuous (contDiff_const.mul F.smooth_speed)
    (F.continuous_lift i) (fun a => (F.support_lift i a).trans Ioc_subset_Icc_self) F.Rpos hb.1 hb.2
  have hc : Continuous (F.marginalWeight i) := by
    have hh : Continuous (uncurry (fun (s : ℝ) (a : UnitAddCircle) => w (s,a))) := hw.1
    change Continuous (fun s => ∫ a, w (s,a) ∂AddCircle.haarAddCircle)
    simpa only [setIntegral_univ] using
      continuous_parametric_integral_of_continuous (X := ℝ) (Y := UnitAddCircle)
        (μ := AddCircle.haarAddCircle) hh isCompact_univ
  refine ⟨hc, (hw.2.image continuous_fst).of_isClosed_subset (isClosed_tsupport _) ?_⟩
  apply closure_minimal ?_ (hw.2.image continuous_fst).isClosed
  intro s hs
  by_contra hn
  have hz (a : UnitAddCircle) : w (s,a) = 0 := by
    by_contra hh
    exact hn ⟨(s,a),subset_tsupport w hh,rfl⟩
  apply hs
  simp only [marginalWeight,show ∀ a, stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
    (fun x => (F.m i:ℝ)*F.V x) (F.A₀ i a) s = 0 from hz,integral_zero]

lemma marginalDensity_nonneg (i : ι) (z : UnitAddCircle) : 0 ≤ F.marginalDensity i z :=
  foldCircleDensity_nonneg (fun s => integral_nonneg (fun _a => branchDensity_nonneg
    (fun _ => sq_nonneg _) s)) z

lemma marginalDensity_measurable (i : ι) : Measurable (F.marginalDensity i) :=
  measurable_foldCircleDensity (F.marginalWeight_regular i).1.measurable

lemma marginalDensity_integrable (i : ι) : Integrable (F.marginalDensity i) AddCircle.haarAddCircle :=
  integrable_foldCircleDensity (F.marginalWeight_regular i).1.measurable
    ((F.marginalWeight_regular i).1.integrable_of_hasCompactSupport (F.marginalWeight_regular i).2)

/-- The actual old packet spectrum, without spare independence. -/
theorem marginalDensity_spectral (i : ι) :
    packetSpectralMeasure (fun u => (F.periodic.lift u:UnitAddCircle)) (F.m i) (F.A i) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (F.marginalDensity i z)) := by
  have hb := scaled_speed_good_branch (F.nonzero i) F.Rpos F.smooth_speed F.positive_deriv
  have hs a : support (F.A₀ i a) ⊆ Ioo (F.l-F.R) (F.u+F.R) := by
    intro x hx
    have hh := F.support_lift i a hx
    constructor <;> linarith [F.Rpos,hh.1,hh.2]
  have he := oldPacket_spectralDensity (m := F.m i) (c := 0) (v := F.periodic.lift)
    (F.continuous_amplitude i) (F.continuous_lift i) (F.lift_matches i)
    (fun a => (F.support_lift i a).trans (by
      intro x hx; exact ⟨lt_of_le_of_lt F.lo hx.1,hx.2.trans F.uo⟩)) hs
    F.speed_continuous.measurable F.smooth_speed (fun _ _ => rfl) isOpen_Ioo Ioo_subset_Icc_self hb.1 hb.2
  change _ = AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal
    (foldCircleDensity (fun s => ∫ a, stationaryWeight (Icc (F.l-F.R) (F.u+F.R))
      (fun x => (F.m i:ℝ)*F.V x) (F.A₀ i a) s ∂AddCircle.haarAddCircle) z))
  simpa only [Int.cast_zero,sub_zero] using he

lemma marginalDensity_carrier (c : ℤ) (i : ι) :
    (F.carrier c).marginalDensity i =ᵐ[AddCircle.haarAddCircle] F.marginalDensity i := by
  have he : AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal ((F.carrier c).marginalDensity i z)) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (F.marginalDensity i z)) := by
    rw [← (F.carrier c).marginalDensity_spectral i,← F.marginalDensity_spectral i]
    congr 1
    funext z
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective z
    exact F.carrier_circle c x
  have h := (withDensity_eq_iff_of_sigmaFinite
    ((F.carrier c).marginalDensity_measurable i).ennreal_ofReal.aemeasurable
    (F.marginalDensity_measurable i).ennreal_ofReal.aemeasurable).mp he
  filter_upwards [h] with z hz
  have hh := congrArg ENNReal.toReal hz
  simpa only [ENNReal.toReal_ofReal ((F.carrier c).marginalDensity_nonneg i z),
    ENNReal.toReal_ofReal (F.marginalDensity_nonneg i z)] using hh

lemma marginalDensity_eq (hmod : F.SpareIndependent) (i : ι) :
    F.marginalDensity i = F.density i := F.density_marginal hmod i

end PassagePackets
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

lemma weight_integrable (i : ι) : Integrable (F.weight i) :=
  (F.weight_regular i).1.continuous.integrable_of_hasCompactSupport (F.weight_regular i).2

lemma density_mass (i : ι) :
    (∫ z, F.density i z ∂AddCircle.haarAddCircle) = ∫ s, F.weight i s :=
  integral_foldCircleDensity (F.weight_regular i).1.continuous.measurable (F.weight_integrable i)

lemma weight_mass_carrier (hmod : F.SpareIndependent) (c : ℤ) (i : ι) :
    (∫ s, (F.carrier c).weight i s) = ∫ s, F.weight i s := by
  rw [← (F.carrier c).density_mass i,F.density_carrier hmod c i,F.density_mass i]

lemma weight_mass_bound [Finite ι] : ∃ B : ℝ, 0 ≤ B ∧ ∀ i, (∫ s, F.weight i s) ≤ B := by
  obtain ⟨B,hB⟩ := (Set.finite_range (fun i => ∫ s, F.weight i s)).isCompact.isBounded.exists_norm_le
  exact ⟨max B 0,le_max_right _ _,fun i => (le_abs_self _).trans
    ((hB _ (mem_range_self i)).trans (le_max_left _ _))⟩

end PassagePackets
end ThreeTorus
end
end

section

/-! Signal transmission on actual iterable packet states. The common prime
modulus and strength bound are fixed before every later finite index type,
scale, state, cutoff, error budget and passage integer. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
universe u

theorem exists_signal_state_family
    {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ α : ℝ, ∃ L : ℕ, ∃ γ₀ : ℝ,
      0 < α ∧ α < b/2 ∧ 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (ι : Type u) [Fintype ι], ∀ (F : PassagePackets ι),
      Injective F.m → F.SpareIndependent → ∀ B : ℝ, 0 < B →
      (∀ i, b ≤ |(F.m i:ℝ)/B|) →
      ∀ ε τ : ℝ, 0 < ε → 0 < τ →
      ∀ᶠ c : ℕ in atTop, 0 < c ∧
      ∃ δ : ℝ, ∃ cut : LawCutoffs δ, ∃ χ : ι → ℝ → ℝ,
      ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      0 < δ ∧ δ < 1/8 ∧
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
              fun z => ∑ j : ↥(S n i), if E j.val then G.density ⟨i,j⟩ z else 0) := by
  classical
  obtain ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,hγ⟩ := exists_actual_signal_family hb hbD hd hdc hdr hd0 hds
  refine ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,?_⟩
  intro γ hγp hγs
  obtain ⟨hdb,hsignal⟩ := hγ γ hγp hγs
  refine ⟨hdb,?_⟩
  intro ι inst F hi hmod B hB hm ε τ hε hτ
  obtain ⟨M,hM,hAM⟩ := F.amplitude_bound
  obtain ⟨W,hW,hWM⟩ := F.weight_mass_bound
  let K := M+W+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hMK : M ≤ K := by dsimp [K]; linarith
  have hWK : W ≤ K := by dsimp [K]; linarith
  let ε₀ := ε/(8*K)
  have hε₀ : 0 < ε₀ := div_pos hε (by positivity)
  obtain ⟨δ,hδ,hδhi⟩ := exists_between (lt_min (by norm_num : (0:ℝ)<1/8)
    (div_pos hε (show 0 < 32*K by positivity)))
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
  filter_upwards [F.tracked_cutoffs hi hmod hτ,hsignal'] with c hc hs
  obtain ⟨hcp,χ,hχ,hdisj⟩ := hc
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
  refine ⟨hcp,δ,cut,χ,Δ,H,hδ,hδ',?_,hdisj,hΔ,hΔt,hHc,hHe,hρs,hρi,hρp,hρm,hgeo,hgraph,hlimit,S,hSd,hTE',?_⟩
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
    obtain ⟨G,hGm,hGA,_hGA₀,hGV,_hGo,_hGl,_hGu,hGmod⟩ := literal_output_packets
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
    refine ⟨G,?_,hGmod,hGV,hGm,hGA,hGden,?_⟩
    · have he : G.m = fun i : PassageOutputIndex (S n) => i.2.val := funext hGm
      rw [he]
      exact output_index_injective (hSd n hn0)
    · intro i E inst
      simp_rw [hGden]
      exact exactRetainedPacketDensity_filtered_singletons hJs isOpen_Ioo (lawJitter_injOn cut hρs.continuous hρi hρp hρm hδ)
        (fun x hx => (hJd x hx).ne') cut.ψ_smooth cut.ψ_compact heψ hsψ (hXs i)
        hHl hHe (F.smooth_amplitude i) hn0 (hSN n hn0 i) E

end ThreeTorus
end
end

section

/-! Support tracking for the actual next packets. Canonical density support
is linked to a genuine old-amplitude point; the same point controls both
normalized angular indices and temporal frequencies. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

namespace PassagePackets
variable {ι : Type*} (F : PassagePackets ι)

lemma speed_bound : ∃ P : ℝ, 0 ≤ P ∧ ∀ x, |F.V x| ≤ P := by
  obtain ⟨P,hP⟩ := (isCompact_range F.speed_continuous).isBounded.exists_norm_le
  exact ⟨max P 0,le_max_right _ _,fun x =>
    (hP _ (mem_range_self (x:UnitAddCircle))).trans (le_max_left _ _)⟩

lemma angular_bound [Finite ι] : ∃ M : ℝ, 0 ≤ M ∧ ∀ i, |(F.m i:ℝ)| ≤ M := by
  obtain ⟨M,hM⟩ := (Set.finite_range (fun i => (F.m i:ℝ))).isCompact.isBounded.exists_norm_le
  exact ⟨max M 0,le_max_right _ _,fun i => (hM _ (mem_range_self i)).trans (le_max_left _ _)⟩

end PassagePackets

lemma periodic_real_bound {J : ℝ → ℝ} (hs : Continuous J) (hp : Periodic J 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |J x| ≤ B := by
  have hc : Continuous hp.lift := by
    apply Continuous.quotient_lift
    exact hs
  obtain ⟨B,hB⟩ := (isCompact_range hc).isBounded.exists_norm_le
  exact ⟨max B 0,le_max_right _ _,fun x =>
    (hB _ (mem_range_self (x:UnitAddCircle))).trans (le_max_left _ _)⟩

/-- The tracked frequency cutoff already controls every retained index, including
zero-amplitude packets. The temporal inequality holds for every new speed point. -/
theorem literal_output_tracking {ι : Type*} {F : PassagePackets ι}
    {S : ι → Finset ℤ} {G : PassagePackets (PassageOutputIndex S)}
    {χ : ι → ℝ → ℝ} {c n : ℕ} {B D P M Q τ : ℝ} {J : ℝ → ℝ}
    (hc : 0 < c) (hn : 0 < n) (hB : 0 < B)
    (hD : ∀ i, |(F.m i:ℝ)/B| ≤ D) (hP : ∀ x, |F.V x| ≤ P)
    (hM : ∀ i, |(F.m i:ℝ)| ≤ M) (hQ : ∀ x, |J x| ≤ Q)
    (hS : ∀ i j, j ∈ S i → χ i ((j:ℝ)/n) ≠ 0)
    (hχ : ∀ i s, s ∈ tsupport (χ i) → ∃ x ∈ F.core i,
      |s-(F.m i:ℝ)*((c:ℝ)+F.V x)| < τ)
    (hm : ∀ i, G.m i = i.2.val) (hV : G.V = fun x => (1+J x/n)/n) :
    ∀ i, ∃ x ∈ F.core i.1,
      |(G.m i:ℝ)/((n:ℝ)*c*B)-(F.m i.1:ℝ)/B| ≤ D*P/c+τ/((c:ℝ)*B) ∧
      ∀ y, dist ((G.m i:ℝ)*G.V y:UnitAddCircle)
        ((F.m i.1:ℝ)*F.V x:UnitAddCircle) ≤ τ+(M*((c:ℝ)+P)+τ)*Q/n := by
  intro i
  obtain ⟨x,hx,htrack⟩ := hχ i.1 _ (subset_tsupport _ (hS i.1 i.2.val i.2.property))
  have hcR : 0 < (c:ℝ) := by exact_mod_cast hc
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hP0 : 0 ≤ P := (abs_nonneg _).trans (hP 0)
  have hs := passage_retained_size hcR.le (hP x) htrack.le
  have hsM : |(i.2.val:ℝ)/n| ≤ M*((c:ℝ)+P)+τ := hs.trans (by
    gcongr
    exact hM i.1)
  refine ⟨x,hx,?_,?_⟩
  · rw [hm i]
    have heq : (i.2.val:ℝ)/((n:ℝ)*c*B) = ((i.2.val:ℝ)/n)/((c:ℝ)*B) := by ring
    rw [heq]
    exact passage_index_drift hcR hB (hD i.1) (hP x) htrack.le
  · intro y
    rw [hm i,hV]
    have heq : (i.2.val:ℝ)*((1+J y/n)/n) = (i.2.val:ℝ)/n+((i.2.val:ℝ)/n)*J y/n := by ring
    rw [heq]
    have ht := passage_temporal_drift (J := J y) (c := (c:ℤ)) hn (by
      simpa only [Int.cast_natCast] using htrack.le)
    apply ht.trans
    exact add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul hsM (hQ y) (abs_nonneg _) ((abs_nonneg _).trans hsM)) hnR.le)

/-- Every nonzero output density is close to an OLD support point. This uses
literal angular indices and speed, not weak convergence of the densities. -/
theorem canonical_output_tracking {ι : Type*} {F : PassagePackets ι}
    {S : ι → Finset ℤ} {G : PassagePackets (PassageOutputIndex S)}
    {χ : ι → ℝ → ℝ} {c n : ℕ} {B D P M Q τ : ℝ} {J : ℝ → ℝ}
    (hc : 0 < c) (hn : 0 < n) (hB : 0 < B)
    (hD : ∀ i, |(F.m i:ℝ)/B| ≤ D) (hP : ∀ x, |F.V x| ≤ P)
    (hM : ∀ i, |(F.m i:ℝ)| ≤ M) (hQ : ∀ x, |J x| ≤ Q)
    (hS : ∀ i j, j ∈ S i → χ i ((j:ℝ)/n) ≠ 0)
    (hχ : ∀ i s, s ∈ tsupport (χ i) → ∃ x ∈ F.core i,
      |s-(F.m i:ℝ)*((c:ℝ)+F.V x)| < τ)
    (hm : ∀ i, G.m i = i.2.val) (hV : G.V = fun x => (1+J x/n)/n) :
    ∀ i z, G.density i z ≠ 0 → ∃ x ∈ F.core i.1,
      |(G.m i:ℝ)/((n:ℝ)*c*B)-(F.m i.1:ℝ)/B| ≤ D*P/c+τ/((c:ℝ)*B) ∧
      dist z ((F.m i.1:ℝ)*F.V x:UnitAddCircle) ≤ τ+(M*((c:ℝ)+P)+τ)*Q/n := by
  intro i z hz
  obtain ⟨x,hx,hidx,ht⟩ := literal_output_tracking hc hn hB hD hP hM hQ hS hχ hm hV i
  obtain ⟨y,_hy,he⟩ := G.density_support i hz
  exact ⟨x,hx,hidx,he ▸ ht y⟩

/-- Large carrier first, small cutoff enlargement second, and final integer
last. The bounded jitter only affects this LAST choice. -/
lemma support_drift_budgets {D P M B e : ℝ} (hB : 0 < B) (he : 0 < e) :
    ∀ᶠ c : ℕ in atTop, 0 < c ∧ ∀ τ : ℝ, 0 < τ → τ < e/2 →
      D*P/c+τ/((c:ℝ)*B) < e ∧
      ∀ Q : ℝ, ∀ᶠ n : ℕ in atTop, 0 < n ∧ τ+(M*((c:ℝ)+P)+τ)*Q/n < e := by
  have hlim : Tendsto (fun c : ℕ => D*P/(c:ℝ)+(e/2)/((c:ℝ)*B)) atTop (𝓝 0) := by
    have hc := tendsto_natCast_atTop_atTop (R := ℝ)
    have h₁ : Tendsto (fun c : ℕ => D*P/(c:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hc
    have h₂ : Tendsto (fun c : ℕ => (e/2)/((c:ℝ)*B)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hc.atTop_mul_const hB)
    simpa using h₁.add h₂
  filter_upwards [eventually_gt_atTop (0:ℕ),hlim.eventually (gt_mem_nhds he)] with c hc hh
  refine ⟨hc,fun τ _hτ hτe => ⟨?_,?_⟩⟩
  · have hcR : 0 < (c:ℝ) := by exact_mod_cast hc
    exact (add_le_add_right (div_le_div_of_nonneg_right hτe.le (mul_pos hcR hB).le) _).trans_lt hh
  · intro Q
    have hlimn : Tendsto (fun n : ℕ => τ+(M*((c:ℝ)+P)+τ)*Q/(n:ℝ)) atTop (𝓝 τ) := by
      simpa using tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)) :
          Tendsto (fun n : ℕ => (M*((c:ℝ)+P)+τ)*Q/(n:ℝ)) atTop (𝓝 0))
    exact (eventually_gt_atTop (0:ℕ)).and (hlimn.eventually (gt_mem_nhds (by linarith)))

end ThreeTorus
end
end

end OAI
