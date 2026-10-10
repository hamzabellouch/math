import Mathlib

namespace OAI

/-! Smooth cylinder cutoffs, circle periodization, and regularity of covering lifts. -/

section

/-! Smooth compact supported cutoffs on the actual real-frequency/slow-circle
cylinder, used for the disjoint stationary images in the passage lemma. -/
noncomputable section
open Set Function Filter Topology
open scoped Topology Manifold
namespace ThreeTorus

/-- A compactly supported Euclidean cutoff, equal to one on a neighborhood
of the prescribed compact set, not merely on the set itself. -/
lemma compact_smooth_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : E → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ U ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      ∀ x ∈ K, f =ᶠ[𝓝 x] 1 := by
  obtain ⟨O,hO,hKO,hOc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨V,hV,hKV,hVU⟩ := hK.exists_isOpen_closure_subset
    ((hU.inter hO).mem_nhdsSet.mpr (subset_inter hKU hKO))
  have hcV : IsCompact (closure V) := hOc.of_isClosed_subset isClosed_closure
    (fun x hx => subset_closure (hVU hx).2)
  obtain ⟨W,hW,hKW,hWV⟩ := hK.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hKV)
  obtain ⟨f,hf,hfr,hfs,hf1⟩ := exists_contMDiff_support_eq_eq_one_iff
    (I := 𝓘(ℝ,E)) (n := (⊤ : ℕ∞)) hV isClosed_closure hWV
  refine ⟨f,hf.contDiff,?_,?_,?_,?_⟩
  · simpa only [HasCompactSupport, tsupport, hfs] using hcV
  · rw [tsupport, hfs]
    intro x hx
    exact (hVU hx).1
  · intro x
    exact hfr (mem_range_self x)
  · intro x hx
    filter_upwards [hW.mem_nhds (hKW hx)] with y hy
    exact (hf1 y).mp (subset_closure hy)

/-- Periodization only in the circle coordinate. -/
def cylinderPeriodize (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∑ᶠ k : ℤ, f (p.1,p.2+k)

lemma cylinderPeriodize_periodic (f : ℝ × ℝ → ℝ) (s : ℝ) :
    Periodic (fun a => cylinderPeriodize f (s,a)) 1 := by
  intro a
  have hh := finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := fun k : ℤ => f (s,a+k))
  simpa [cylinderPeriodize,add_comm,add_left_comm,add_assoc] using hh

lemma cylinderPeriodize_local_support {f : ℝ × ℝ → ℝ}
    (hc : HasCompactSupport f) (p : ℝ × ℝ) :
    ∃ S : Finset ℤ, ∀ᶠ q in 𝓝 p, support (fun k : ℤ => f (q.1,q.2+k)) ⊆ (S : Set ℤ) := by
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R+|p.2|+1)
  refine ⟨Finset.Icc (-(N:ℤ)) N,?_⟩
  filter_upwards [continuous_snd.tendsto p (Metric.ball_mem_nhds p.2 (by norm_num : (0:ℝ)<1))] with q hq
  intro k hk
  have hq' : |q.2| < |p.2|+1 := by
    have hh := abs_add_le (q.2-p.2) p.2
    have hi : |q.2-p.2| < 1 := hq
    simpa only [sub_add_cancel] using hh.trans_lt (by linarith : |q.2-p.2|+|p.2| < |p.2|+1)
  have hk' : |q.2+(k:ℝ)| ≤ R :=
    (norm_snd_le (q.1,q.2+(k:ℝ))).trans (hR _ (subset_tsupport f hk))
  have hz : |(k:ℝ)| < (N:ℝ) := calc
    |(k:ℝ)| = |(q.2+k)-q.2| := by congr 1; ring
    _ ≤ |q.2+k|+|q.2| := abs_sub _ _
    _ < (N:ℝ) := by linarith
  rw [Finset.mem_coe,Finset.mem_Icc]
  exact_mod_cast (abs_le.mp hz.le)

lemma contDiff_cylinderPeriodize {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hc : HasCompactSupport f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cylinderPeriodize f) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro p
  obtain ⟨S,hS⟩ := cylinderPeriodize_local_support hc p
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => ∑ k ∈ S, f (q.1,q.2+k)) :=
    ContDiff.sum (fun _ _ => hf.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const)))
  apply hh.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hS] with q hq
  exact finsum_eq_sum_of_support_subset _ hq

/-- The covering map for the real-frequency/slow-circle cylinder. -/
def cylinderProjection (p : ℝ × ℝ) : ℝ × UnitAddCircle := (p.1,(p.2 : UnitAddCircle))

lemma continuous_cylinderProjection : Continuous cylinderProjection :=
  continuous_fst.prodMk (QuotientAddGroup.continuous_mk.comp continuous_snd)

lemma cylinderProjection_surjective : Surjective cylinderProjection := by
  rintro ⟨s,a⟩
  obtain ⟨b,hb⟩ := QuotientAddGroup.mk_surjective a
  exact ⟨(s,b),Prod.ext rfl hb⟩

lemma isOpenMap_cylinderProjection : IsOpenMap cylinderProjection := by
  exact IsOpenMap.id.prodMap QuotientAddGroup.isOpenMap_coe

lemma isQuotientMap_cylinderProjection : IsQuotientMap cylinderProjection :=
  isOpenMap_cylinderProjection.isQuotientMap continuous_cylinderProjection cylinderProjection_surjective

/-- Smoothness on this cylinder is smoothness of the periodic covering lift. -/
def CylinderSmooth (f : ℝ × UnitAddCircle → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ cylinderProjection)

lemma CylinderSmooth.continuous {f : ℝ × UnitAddCircle → ℝ} (hf : CylinderSmooth f) :
    Continuous f := isQuotientMap_cylinderProjection.continuous_iff.mpr (ContDiff.continuous hf)

/-- Periodization with a smooth saturation gives a [0,1]-valued cylinder function. -/
def cylinderCutoff (f : ℝ × ℝ → ℝ) (p : ℝ × UnitAddCircle) : ℝ :=
  Real.smoothTransition ((cylinderPeriodize_periodic f p.1).lift p.2)

@[simp] lemma cylinderCutoff_coe (f : ℝ × ℝ → ℝ) (s a : ℝ) :
    cylinderCutoff f (s,(a : UnitAddCircle)) =
      Real.smoothTransition (cylinderPeriodize f (s,a)) := rfl

lemma cylinderCutoff_smooth {f : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hc : HasCompactSupport f) :
    CylinderSmooth (cylinderCutoff f) :=
  Real.smoothTransition.contDiff.comp (contDiff_cylinderPeriodize hf hc)

lemma cylinderCutoff_mem_Icc (f : ℝ × ℝ → ℝ) (p : ℝ × UnitAddCircle) :
    0 ≤ cylinderCutoff f p ∧ cylinderCutoff f p ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

lemma cylinderPeriodize_finite {f : ℝ × ℝ → ℝ} (hc : HasCompactSupport f) (p : ℝ × ℝ) :
    HasFiniteSupport (fun k : ℤ => f (p.1,p.2+k)) := by
  obtain ⟨S,hS⟩ := cylinderPeriodize_local_support hc p
  exact S.finite_toSet.subset (hS.self_of_nhds)

lemma cylinderCutoff_one_of_eq_one {f : ℝ × ℝ → ℝ} (hc : HasCompactSupport f)
    (hf : ∀ p, 0 ≤ f p) {p : ℝ × ℝ} (hp : f p = 1) :
    cylinderCutoff f (cylinderProjection p) = 1 := by
  apply Real.smoothTransition.one_of_one_le
  change 1 ≤ ∑ᶠ k : ℤ, f (p.1,p.2+k)
  have hfin : (support (fun k : ℤ => f (p.1,p.2+k))).Finite :=
    cylinderPeriodize_finite hc p
  rw [finsum_eq_sum _ hfin]
  have hz : (0:ℤ) ∈ hfin.toFinset := by simp [mem_support, hp]
  simpa [hp] using Finset.single_le_sum (fun (k : ℤ) _ => hf (p.1,p.2+k)) hz

lemma cylinderCutoff_support_subset {f : ℝ × ℝ → ℝ} :
    support (cylinderCutoff f) ⊆ cylinderProjection '' support f := by
  intro p hp
  obtain ⟨q,rfl⟩ := cylinderProjection_surjective p
  have hh : cylinderPeriodize f q ≠ 0 := by
    intro hz
    exact hp (by simp [cylinderProjection,cylinderCutoff_coe,hz])
  obtain ⟨k,hk⟩ : ∃ k : ℤ, f (q.1,q.2+k) ≠ 0 := by
    by_contra h
    push Not at h
    exact hh (by simp [cylinderPeriodize,h])
  refine ⟨(q.1,q.2+k),hk,?_⟩
  dsimp [cylinderProjection]
  congr 1
  simp

lemma cylinderCutoff_tsupport_subset {f : ℝ × ℝ → ℝ} (hc : HasCompactSupport f) :
    tsupport (cylinderCutoff f) ⊆ cylinderProjection '' tsupport f := by
  apply closure_minimal
  · exact cylinderCutoff_support_subset.trans (image_mono subset_closure)
  · exact (hc.image continuous_cylinderProjection).isClosed

lemma cylinderCutoff_compactSupport {f : ℝ × ℝ → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (cylinderCutoff f) :=
  (hc.image continuous_cylinderProjection).of_isClosed_subset isClosed_closure
    (cylinderCutoff_tsupport_subset hc)

lemma cylinderCutoff_one_near {f : ℝ × ℝ → ℝ} (hc : HasCompactSupport f)
    (hf : ∀ p, 0 ≤ f p) {p : ℝ × ℝ} (hp : f =ᶠ[𝓝 p] 1) :
    cylinderCutoff f =ᶠ[𝓝 (cylinderProjection p)] 1 := by
  obtain ⟨V,hV,hVo,hpV⟩ := mem_nhds_iff.mp hp
  apply Filter.mem_of_superset
    ((isOpenMap_cylinderProjection _ hVo).mem_nhds (mem_image_of_mem _ hpV))
  rintro _ ⟨q,hq,rfl⟩
  exact cylinderCutoff_one_of_eq_one hc hf (hV hq)

lemma compact_cylinder_lift {K : Set (ℝ × UnitAddCircle)} (hK : IsCompact K) :
    ∃ L : Set (ℝ × ℝ), IsCompact L ∧ cylinderProjection '' L = K := by
  obtain ⟨R,hR⟩ := (hK.image continuous_fst).isBounded.exists_norm_le
  let B : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc 0 1
  let L := B ∩ cylinderProjection ⁻¹' K
  refine ⟨L,(isCompact_Icc.prod isCompact_Icc).inter_right
    (hK.isClosed.preimage continuous_cylinderProjection),?_⟩
  apply Subset.antisymm
  · rintro _ ⟨p,hp,rfl⟩
    exact hp.2
  · intro p hp
    obtain ⟨a,ha,hae⟩ := AddCircle.eq_coe_Ico p.2
    have hs : p.1 ∈ Icc (-R) R := abs_le.mp (hR _ (mem_image_of_mem _ hp))
    refine ⟨(p.1,a),⟨⟨hs,⟨ha.1,ha.2.le⟩⟩,?_⟩,?_⟩
    · simpa [cylinderProjection,hae] using hp
    · exact Prod.ext rfl hae

/-- The exact smooth cutoff needed for a compact stationary image in the cylinder.
The support may be placed in an arbitrary prescribed open neighborhood. -/
theorem compact_cylinder_cutoff {K U : Set (ℝ × UnitAddCircle)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : ℝ × UnitAddCircle → ℝ, CylinderSmooth χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ p, 0 ≤ χ p ∧ χ p ≤ 1) ∧
      ∀ p ∈ K, χ =ᶠ[𝓝 p] 1 := by
  obtain ⟨L,hL,hLK⟩ := compact_cylinder_lift hK
  obtain ⟨f,hf,hfc,hfs,hfr,hf1⟩ := compact_smooth_cutoff hL
    (hU.preimage continuous_cylinderProjection)
    (fun p hp => hKU (hLK ▸ mem_image_of_mem cylinderProjection hp))
  refine ⟨cylinderCutoff f,cylinderCutoff_smooth hf hfc,
    cylinderCutoff_compactSupport hfc,?_,cylinderCutoff_mem_Icc f,?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := cylinderCutoff_tsupport_subset hfc hp
    exact hfs hq
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := hLK.symm ▸ hp
    exact cylinderCutoff_one_near hfc (fun q => (hfr q).1) (hf1 q hq)

/-- Finite disjoint compact stationary images admit simultaneous smooth
cutoffs with disjoint compact supports, in any prescribed neighborhoods. -/
theorem finite_disjoint_cylinder_cutoffs {ι : Type*} [Finite ι]
    (K U : ι → Set (ℝ × UnitAddCircle))
    (hK : ∀ i, IsCompact (K i)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, K i ⊆ U i) (hdisj : Pairwise (Disjoint on K)) :
    ∃ χ : ι → ℝ × UnitAddCircle → ℝ,
      (∀ i, CylinderSmooth (χ i) ∧ HasCompactSupport (χ i) ∧ tsupport (χ i) ⊆ U i ∧
        (∀ p, 0 ≤ χ i p ∧ χ i p ≤ 1) ∧ ∀ p ∈ K i, χ i =ᶠ[𝓝 p] 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) := by
  have hd : Pairwise (fun i j => Disjoint (𝓝ˢ (K i)) (𝓝ˢ (K j))) :=
    fun i j hij => disjoint_nhdsSet_nhdsSet (hK i).isClosed (hK j).isClosed (hdisj hij)
  obtain ⟨O,hO,hOd⟩ := hd.exists_mem_filter_of_disjoint
  have hv i : K i ⊆ interior (O i) ∩ U i :=
    subset_inter (subset_interior_iff_mem_nhdsSet.mpr (hO i)) (hKU i)
  choose χ hχ using fun i => compact_cylinder_cutoff (hK i)
    (isOpen_interior.inter (hU i)) (hv i)
  refine ⟨χ,fun i => ⟨(hχ i).1,(hχ i).2.1,(hχ i).2.2.1.trans inter_subset_right,
    (hχ i).2.2.2⟩,?_⟩
  intro i j hij
  exact (hOd hij).mono ((hχ i).2.2.1.trans (inter_subset_left.trans interior_subset))
    ((hχ j).2.2.1.trans (inter_subset_left.trans interior_subset))

/-- Compact support away from the zero frequency leaves finitely many
nonzero angular indices at every positive integral scale. -/
lemma cylinder_cutoff_finite_indices {χ : ℝ × UnitAddCircle → ℝ}
    (hc : HasCompactSupport χ) (hzero : ∀ a, χ (0,a) = 0) (n : ℕ) (hn : 0 < n) :
    ∃ S : Finset ℤ, (0:ℤ) ∉ S ∧ ∀ j ∉ S, ∀ a, χ ((j:ℝ)/n,a) = 0 := by
  classical
  obtain ⟨R,hR⟩ := (hc.image continuous_fst).isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt ((n:ℝ)*R)
  refine ⟨(Finset.Icc (-(N:ℤ)) N).erase 0,Finset.notMem_erase _ _,?_⟩
  intro j hj a
  by_contra ha
  have hj0 : j ≠ 0 := by intro hz; subst j; simp [hzero] at ha
  have hb : |(j:ℝ)/(n:ℝ)| ≤ R :=
    hR _ (mem_image_of_mem Prod.fst (subset_tsupport χ ha))
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [abs_div,abs_of_pos hn'] at hb
  have hjN : |(j:ℝ)| < N := ((div_le_iff₀ hn').mp hb).trans_lt (by nlinarith)
  apply hj
  rw [Finset.mem_erase,Finset.mem_Icc]
  exact ⟨hj0,by exact_mod_cast (abs_le.mp hjN.le)⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter Topology
open scoped Topology BigOperators
namespace ThreeTorus

/-- Periodization in the REAL coordinate of a compact cylinder cutoff. -/
def cylinderFirstPeriodize (χ : ℝ × UnitAddCircle → ℝ) (p : ℝ × UnitAddCircle) : ℝ :=
  ∑ᶠ k : ℤ, χ (p.1+k,p.2)

lemma cylinderFirstPeriodize_periodic (χ : ℝ × UnitAddCircle → ℝ) (a : UnitAddCircle) :
    Periodic (fun u => cylinderFirstPeriodize χ (u,a)) 1 := by
  intro u
  have hh := finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := fun k : ℤ => χ (u+k,a))
  simpa [cylinderFirstPeriodize,add_comm,add_left_comm,add_assoc] using hh

lemma cylinderFirstPeriodize_local_support {χ : ℝ × UnitAddCircle → ℝ}
    (hc : HasCompactSupport χ) (p : ℝ × ℝ) :
    ∃ S : Finset ℤ, ∀ᶠ q in 𝓝 p,
      support (fun k : ℤ => χ (q.1+k,(q.2:UnitAddCircle))) ⊆ (S : Set ℤ) := by
  obtain ⟨R,hR⟩ := (hc.image continuous_fst).isBounded.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt (R+|p.1|+1)
  refine ⟨Finset.Icc (-(N:ℤ)) N,?_⟩
  filter_upwards [continuous_fst.tendsto p (Metric.ball_mem_nhds p.1 (by norm_num : (0:ℝ)<1))] with q hq
  intro k hk
  have hq' : |q.1| < |p.1|+1 := by
    have hh := abs_add_le (q.1-p.1) p.1
    have hi : |q.1-p.1| < 1 := hq
    simpa only [sub_add_cancel] using hh.trans_lt (by linarith : |q.1-p.1|+|p.1| < |p.1|+1)
  have hk' : |q.1+(k:ℝ)| ≤ R := hR _ (mem_image_of_mem _ (subset_tsupport χ hk))
  have hz : |(k:ℝ)| < (N:ℝ) := calc
    |(k:ℝ)| = |(q.1+k)-q.1| := by congr 1; ring
    _ ≤ |q.1+k|+|q.1| := abs_sub _ _
    _ < (N:ℝ) := by linarith
  rw [Finset.mem_coe,Finset.mem_Icc]
  exact_mod_cast (abs_le.mp hz.le)

lemma cylinderFirstPeriodize_smooth {χ : ℝ × UnitAddCircle → ℝ}
    (hχ : CylinderSmooth χ) (hc : HasCompactSupport χ) :
    CylinderSmooth (cylinderFirstPeriodize χ) := by
  classical
  rw [CylinderSmooth, contDiff_iff_contDiffAt]
  intro p
  obtain ⟨S,hS⟩ := cylinderFirstPeriodize_local_support hc p
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => ∑ k ∈ S, χ (q.1+k,(q.2:UnitAddCircle))) :=
    ContDiff.sum (fun _ _ => hχ.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd))
  apply hh.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hS] with q hq
  exact finsum_eq_sum_of_support_subset _ hq

/-- The cutoff on the actual two-torus, not a chart-only surrogate. -/
def cylinderTorusCutoff (χ : ℝ × UnitAddCircle → ℝ) (p : UnitAddCircle × UnitAddCircle) : ℝ :=
  (cylinderFirstPeriodize_periodic χ p.2).lift p.1

@[simp] lemma cylinderTorusCutoff_coe (χ : ℝ × UnitAddCircle → ℝ) (u : ℝ) (a : UnitAddCircle) :
    cylinderTorusCutoff χ ((u:UnitAddCircle),a) = cylinderFirstPeriodize χ (u,a) := rfl

lemma cylinderTorusCutoff_smooth {χ : ℝ × UnitAddCircle → ℝ}
    (hχ : CylinderSmooth χ) (hc : HasCompactSupport χ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => cylinderTorusCutoff χ ((p.1:UnitAddCircle),(p.2:UnitAddCircle))) :=
  cylinderFirstPeriodize_smooth hχ hc

lemma cylinderTorusCutoff_continuous {χ : ℝ × UnitAddCircle → ℝ}
    (hχ : CylinderSmooth χ) (hc : HasCompactSupport χ) :
    Continuous (cylinderTorusCutoff χ) := by
  have hq : IsQuotientMap (fun p : ℝ × UnitAddCircle => ((p.1:UnitAddCircle),p.2)) :=
    (QuotientAddGroup.isOpenMap_coe.prodMap IsOpenMap.id).isQuotientMap
      (QuotientAddGroup.continuous_mk.prodMap continuous_id)
      (QuotientAddGroup.mk_surjective.prodMap surjective_id)
  apply hq.continuous_iff.mpr
  exact (cylinderFirstPeriodize_smooth hχ hc).continuous

lemma cylinderFirstPeriodize_eq {χ : ℝ × UnitAddCircle → ℝ} {o : ℝ}
    (hs : support χ ⊆ Ioo o (o+1) ×ˢ univ) {u : ℝ} (hu : u ∈ Ioc o (o+1))
    (a : UnitAddCircle) : cylinderFirstPeriodize χ (u,a) = χ (u,a) := by
  classical
  unfold cylinderFirstPeriodize
  have hz : ∀ k : ℤ, k ≠ 0 → χ (u+k,a) = 0 := by
    intro k hk
    apply notMem_support.mp
    intro hh
    have h := (hs hh).1
    rcases lt_or_gt_of_ne hk with hk' | hk'
    · have hk'' : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      linarith [h.1,hu.2]
    · have hk'' : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      linarith [h.2,hu.1]
  rw [finsum_eq_single _ 0 (fun k hk => hz k hk)]
  simp

lemma cylinderTorusCutoff_eq {χ : ℝ × UnitAddCircle → ℝ} {o : ℝ}
    (hs : support χ ⊆ Ioo o (o+1) ×ˢ univ) {u : ℝ} (hu : u ∈ Ioc o (o+1))
    (a : UnitAddCircle) : cylinderTorusCutoff χ ((u:UnitAddCircle),a) = χ (u,a) :=
  cylinderFirstPeriodize_eq hs hu a

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter Topology
open scoped Topology
namespace ThreeTorus

/-- Cover smoothness supplies the parameter-continuous first derivatives
needed by stationary phase on a cylinder; it is not an additional regularity
assumption on the clipped packets. -/
lemma cylinder_smooth_regular {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × UnitAddCircle → E}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ cylinderProjection)) :
    (∀ a, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f (x,a))) ∧
    Continuous f ∧ Continuous (fun p : ℝ × UnitAddCircle => deriv (fun x => f (x,p.2)) p.1) := by
  have ht a : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => f (x,a)) := by
    obtain ⟨b,rfl⟩ := QuotientAddGroup.mk_surjective a
    exact hf.comp (contDiff_id.prodMk contDiff_const)
  refine ⟨ht,isQuotientMap_cylinderProjection.continuous_iff.mpr hf.continuous,?_⟩
  apply isQuotientMap_cylinderProjection.continuous_iff.mpr
  have he (p : ℝ × ℝ) : deriv (fun x : ℝ => f (x,(p.2:UnitAddCircle))) p.1 =
      fderiv ℝ (f ∘ cylinderProjection) p (1,0) := by
    have hd : HasFDerivAt (f ∘ cylinderProjection) (fderiv ℝ (f ∘ cylinderProjection) p) p :=
      (hf.differentiable (by simp) p).hasFDerivAt
    have hh := hd.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
    simpa only [Function.comp_def,cylinderProjection,id_eq] using hh.deriv
  change Continuous (fun p : ℝ × ℝ => deriv (fun x : ℝ => f (x,(p.2:UnitAddCircle))) p.1)
  simp_rw [he]
  exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const

end ThreeTorus
end
end

end OAI
