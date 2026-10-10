import OAI.Geometry.Convex.GeneralMahler.Normalize
import OAI.Geometry.Convex.GeneralMahler.Rigid.Rays
import OAI.Geometry.Convex.GeneralMahler.SimplexVolume

namespace OAI
/-! Geometric Mahler bounds from cone Laplace integrals and profile inequalities. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric Module
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Profile Segment
structure Input091 : Prop where
  ly : LayerOK
  ud : UpdatesOK Cp Kp
  sg : SegmentOK

variable {m:ℕ} [NeZero m]
omit [NeZero m] in
lemma orthant_pull {E F:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {C:ProperCone ℝ E} {D:ProperCone ℝ F} (B:E≃ₗ[ℝ]F) (hB:∀ x,x∈C↔B x∈D)
    (h:IsLinearOrthant m D) : IsLinearOrthant m C := by
  obtain ⟨a,rfl⟩:=h
  let b:= a.map B.symm
  refine ⟨b,?_⟩
  ext x; rw [hB,mem_orthant,mem_orthant]
  have he : b.equivFun x=a.equivFun (B x) := by unfold b; rw [Basis.map_equivFun]; rfl
  rw [he]

lemma ConeLap (h:Input091) (C:ProperCone ℝ (Rn m)) (U V:Rn m)
    (hU:U∈interior (C:Set (Rn m))) (hV:V∈interior (posDual C:Set (Rn m))) (he:⟪U,V⟫=(m:ℝ)):
    1 ≤ chi C V*chi (posDual C) U ∧
      (chi C V*chi (posDual C) U=1 → IsLinearOrthant m C) := by
  let q:ProjField m:={
    C:=C,U:=U,V:=V,U_in:=hU,V_in:=hV,ip:=he,S:=1,pos:=Matrix.PosDef.one,
    root:=equivPD Matrix.PosDef.one, matrix_eq:=equivPD_spec _
  }
  obtain ⟨R,hR,hR',P,hP⟩:= simultaneous q h.ud
  let W:= P.instanceQ hR' q
  have hh : W.Balanced P.T :=
    ⟨P.in_box.2,(P.sigma_choice hR' q).symm,hP.2.1,hP.1,hP.2.2⟩
  let B := (P.transE hR').toLinearEquiv
  have h₁ : chi W.C W.V*chi W.D W.U = chi C V*chi (posDual C) U :=
    chi_transform B C U V
  obtain ⟨hf,hf'⟩:= W.C_bound P.T hh h.ud h.ly h.sg
  rw [h₁] at hf hf'
  refine ⟨hf,fun H=>orthant_pull B ?_ (hf' H)⟩
  intro x; change x∈C↔B x∈pushCone B C; rw [mem_pushCone,LinearEquiv.symm_apply_apply]

namespace Body
variable {n:ℕ}

-- transfer through an isometric identification with Rn(n+1)
lemma CLift (h:Input091) (C:ProperCone ℝ (LiftSpace n)) (U V:LiftSpace n)
    (hU:U∈interior (C:Set (LiftSpace n))) (hV:V∈interior (posDual C:Set (LiftSpace n)))
    (he:⟪U,V⟫=((n+1:ℕ):ℝ)):
    1 ≤ chi C V*chi (posDual C) U ∧
      (chi C V*chi (posDual C) U=1 → IsLinearOrthant (n+1) C) := by
  let a : OrthonormalBasis (Fin (n+1)) ℝ (LiftSpace n) :=
    (stdOrthonormalBasis ℝ _).reindex (finCongr (lift_finrank n))
  let B:= a.repr
  let M:=a.measurableEquiv
  have hB : MeasurePreserving M := a.measurePreserving_measurableEquiv
  let p := fun D: ProperCone ℝ (LiftSpace n)=> ProperCone.comap
    B.symm.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap D
  have hp (D) (x:LiftSpace n): B x ∈ p D ↔ x∈D := by
    change B.symm (B x)∈D↔_
    rw [B.symm_apply_apply]
  have hi (D:ProperCone ℝ (LiftSpace n)) (x:LiftSpace n) (hx:x∈interior (D:Set (LiftSpace n))):
      B x∈interior ((p D):Set (Rn (n+1))) := by
    let k:= B.toLinearEquiv.toContinuousLinearEquiv.toHomeomorph
    change k x ∈ interior (k.symm ⁻¹' (D:Set (LiftSpace n)))
    rw [← k.symm.preimage_interior]
    simpa using hx
  have hh : posDual (p C) = p (posDual C) := by
    ext x
    obtain ⟨x,rfl⟩:=B.surjective x
    rw [hp,mem_posDual,mem_posDual]
    constructor
    · intro h y hy
      have hj:= h ((hp C y).2 hy); rwa [B.inner_map_map] at hj
    intro h y hy
    obtain ⟨y,rfl⟩:=B.surjective y
    rw [B.inner_map_map]; exact h ((hp C y).mp hy)
  have hc (D) (w:LiftSpace n): chi (p D) (B w)=chi D w := by
    classical
    unfold chi
    rw [← integral_indicator (p D).isClosed.measurableSet,
      ← integral_indicator D.isClosed.measurableSet,← hB.integral_comp']
    congr 1; ext x
    change ((p D):Set (Rn (n+1))).indicator _ (B x)=_
    by_cases h:x∈D
    · rw [indicator_of_mem ((hp D x).2 h),indicator_of_mem h]; rw [B.inner_map_map]
    rw [indicator_of_notMem (mt ((hp D x).1) h), indicator_of_notMem h]
  obtain ⟨h,h'⟩:= ConeLap h (p C) (B U) (B V) (hi _ U hU) (by rw [hh]; apply hi _ V hV)
    (by rw [B.inner_map_map,he])
  rw [hh,hc,hc] at h h'
  exact ⟨h,fun he=> orthant_pull B.toLinearEquiv (fun x=> (hp C x).symm) (h' he)⟩

lemma bound_at (h:Input091) (K:Body n) (z:Rn n) (hz:z∈interior (K:Set (Rn n))):
    ((n:ℝ)+1)^(n+1)/(n.factorial:ℝ)^2 ≤ K.productAt z ∧
      (K.productAt z=((n:ℝ)+1)^(n+1)/(n.factorial:ℝ)^2 → IsSimplex (K:Set (Rn n))) := by
  let m:ℝ:= (n:ℝ)+1
  have hm : 0 < m := by unfold m; positivity
  let U:=pair m (m • z)
  let V:=pair 1 (0:Rn n)
  have he : ⟪U,V⟫=((n+1:ℕ):ℝ) := by unfold U V; rw [pair_inner]; simp [m]
  obtain ⟨hh,hi⟩:=CLift h K.cone U V ((K.pair_mem_interior_cone_iff m hm _).2 hz)
    (axis_dual_interior K 1 zero_lt_one) he
  let k : ℝ := m^(n+1)/(n.factorial:ℝ)^2
  have hk : 0<k := by unfold k; positivity
  have H : chi K.cone V*chi (posDual K.cone) U= K.productAt z/k := by
    rw [cone_volume K z hz m hm]
    unfold k productAt polarVol
    rw [inv_pow]; field_simp
  rw [H] at hh hi
  change k≤ _ ∧ ((K.productAt z)=k → IsSimplex _)
  refine ⟨?_,fun he=>simplex_of_linearOrthant (hi (by rw [he,div_self hk.ne']))⟩
  rw [le_div_iff₀ hk,one_mul] at hh; exact hh

theorem main_with_profiles (h:Input091) (K:Body n) :
    ((n:ℝ)+1)^(n+1)/(n.factorial:ℝ)^2 ≤ K.P ∧
      (K.P=((n:ℝ)+1)^(n+1)/(n.factorial:ℝ)^2 ↔ IsSimplex (K:Set (Rn n))) := by
  obtain ⟨hh,hi⟩:= bound_at h K K.santalo K.santalo_spec.1
  exact ⟨hh,hi,@simplex_attains n K⟩
end Body
end GeneralMahler

end

end OAI
