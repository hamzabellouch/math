import OAI.NumberTheory.DukePrimeDegree.Geometry.RootCompactTransversals

namespace OAI

/-! # Physical rectangles containing prescribed compact orbit pieces -/

noncomputable section
open Matrix Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_shifted_root_rectangle_covering_compact
    {T B : Type*} [TopologicalSpace T] [TopologicalSpace B]
    {D : Set (T × B)} (hD : IsOpen D)
    {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (e : D → RootSlice a b k) (he : Topology.IsOpenEmbedding e)
    (τ : D → ℝ) (hτ : Continuous τ) (s : T)
    (hsD : {s} ×ˢ (univ : Set B) ⊆ D)
    (hinj : Set.InjOn (fun z : D × ℝ => rootQuotientParametrization hab (e z.1,z.2))
      ({z : D | z.val.1 = s} ×ˢ univ))
    (K : Set B) (hK : IsCompact K) (I : Set ℝ) (hI : IsCompact I) (hne : I.Nonempty)
    (V : Set B) (hV : IsOpen V) (hKV : K ⊆ V)
    (I₀ : Set ℝ) (hI₀ : IsOpen I₀) (hII₀ : I ⊆ I₀) :
    ∃ (Q : RootTransverseRectangle D) (A : RootBox hab k) (R : ℝ) (J : Set ℝ),
      IsOpen J ∧ s ∈ Q.first ∧ K ⊆ Q.second ∧ I ⊆ J ∧
      Q.second ⊆ V ∧ J ⊆ I₀ ∧
      A.transverse = range (e ∘ Q.inclusion) ∧ A.time ⊆ rootLeafWindow R 0 ∧
      ∀ w : Q.first × Q.second, (Homeomorph.addRight (τ (Q.inclusion w))) '' J ⊆ A.time := by
  let f : K → D := fun w => ⟨(s,w.val),hsD ⟨rfl,mem_univ _⟩⟩
  have hf : Continuous f :=
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let P : Set D := range f
  have hP : IsCompact P := isCompact_range hf
  have hS : IsCompact (e '' P) := hP.image he.continuous
  have hi : Set.InjOn (rootQuotientParametrization hab) ((e '' P) ×ˢ univ) := by
    rintro ⟨x,t⟩ ⟨⟨z,⟨w,rfl⟩,rfl⟩,_⟩ ⟨y,u⟩ ⟨⟨z',⟨w',rfl⟩,rfl⟩,_⟩ h
    have H := hinj (x₁ := (f w,t)) (x₂ := (f w',u))
      ⟨rfl,mem_univ _⟩ ⟨rfl,mem_univ _⟩ h
    exact congrArg (fun z : D × ℝ => (e z.1,z.2)) H
  let F : D × ℝ → RootSlice a b k × ℝ := fun z => (e z.1,z.2 + τ z.1)
  have hF : Continuous F := (he.continuous.comp continuous_fst).prodMk
    (continuous_snd.add (hτ.comp continuous_fst))
  have hb : IsCompact ((fun z : D × ℝ => z.2 + τ z.1) '' (P ×ˢ I)) :=
    (hP.prod hI).image (continuous_snd.add (hτ.comp continuous_fst))
  obtain ⟨R,_,hR⟩ := hb.isBounded.exists_pos_norm_lt
  have hRI : ∀ z ∈ P ×ˢ I, z.2 + τ z.1 ∈ Ioo (-R) R := by
    intro z hz
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hR _ ⟨z,hz,rfl⟩)
  obtain ⟨A,hSA,hIA⟩ := rootBox_contains_compact_transverse hab (e '' P) hS hi
    (Icc (-R) R) isCompact_Icc
  let W := A.time ∩ Ioo (-R) R
  have hW : IsOpen W := A.time_open.inter isOpen_Ioo
  have hPW : P ×ˢ I ⊆ F ⁻¹' (A.transverse ×ˢ W) := by
    intro z hz
    exact ⟨hSA ⟨z.1,hz.1,rfl⟩,hIA (Ioo_subset_Icc_self (hRI z hz)),hRI z hz⟩
  obtain ⟨Z,J,hZ,hJ,hPZ,hIJ,hZJ⟩ := generalized_tube_lemma hP hI
    ((A.transverse_open.prod hW).preimage hF) hPW
  have hZO : IsOpen ((Subtype.val '' Z) ∩ (univ ×ˢ V)) :=
    (hD.isOpenEmbedding_subtypeVal.isOpenMap Z hZ).inter (isOpen_univ.prod hV)
  have hsKO : {s} ×ˢ K ⊆ (Subtype.val '' Z) ∩ (univ ×ˢ V) := by
    rintro ⟨u,w⟩ ⟨hu,hw⟩
    have hu' : u=s := hu
    subst u
    exact ⟨⟨f ⟨w,hw⟩,hPZ ⟨⟨w,hw⟩,rfl⟩,rfl⟩,mem_univ _,hKV hw⟩
  obtain ⟨U,V',hU,hV',hsU,hKV',hUV'⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({s} : Set T)) hK hZO hsKO
  let Q : RootTransverseRectangle D := ⟨U,V',hU,hV',by
    intro z hz
    obtain ⟨v,_,hv⟩ := (hUV' hz).1
    exact hv ▸ v.prop⟩
  have hQZ : ∀ w : Q.first × Q.second, Q.inclusion w ∈ Z := by
    intro w
    obtain ⟨v,hv,heq⟩ := (hUV'
      (show (w.1.val,w.2.val) ∈ U ×ˢ V' from ⟨w.1.prop,w.2.prop⟩)).1
    have hv' : v=Q.inclusion w := Subtype.ext heq
    exact hv' ▸ hv
  obtain ⟨t,ht⟩ := hne
  have hsub : range (e ∘ Q.inclusion) ⊆ A.transverse := by
    rintro _ ⟨w,rfl⟩
    exact (hZJ (show (Q.inclusion w,t) ∈ Z ×ˢ J from ⟨hQZ w,hIJ ht⟩)).1
  let A' := A.shrink (range (e ∘ Q.inclusion)) W
    (he.comp (Q.inclusion_isOpenEmbedding hD)).isOpen_range hW hsub inter_subset_left
  refine ⟨Q,A',R,J ∩ I₀,hJ.inter hI₀,hsU rfl,hKV',
    fun _ ht => ⟨hIJ ht,hII₀ ht⟩,?_,inter_subset_right,rfl,?_,?_⟩
  · intro w hw
    exact (hUV' (show (s,w) ∈ U ×ˢ V' from ⟨hsU (Set.mem_singleton s),hw⟩)).2.2
  · intro u hu
    simpa only [rootLeafWindow,Nat.cast_zero,add_zero] using hu.2
  · intro w u hu
    obtain ⟨r,hr,rfl⟩ := hu
    exact (hZJ (show (Q.inclusion w,r) ∈ Z ×ˢ J from ⟨hQZ w,hr.1⟩)).2

end DukePrimeDegree

end

end OAI
