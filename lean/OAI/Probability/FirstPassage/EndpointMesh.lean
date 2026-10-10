import OAI.Probability.FirstPassage.GridMeshes

namespace OAI

namespace PlanarFPP

noncomputable def meshFloor (x d : ℤ) : ℤ := x / d * d

lemma meshFloor_bounds (x d : ℤ) (hd : 0 < d) :
    meshFloor x d ≤ x ∧ x < meshFloor x d+d := by
  have h0 := Int.emod_nonneg x (ne_of_gt hd)
  have h1 := Int.emod_lt_of_pos x hd
  have he := Int.emod_add_ediv_mul x d
  dsimp [meshFloor]
  omega

lemma meshFloor_dvd (x d : ℤ) : d ∣ meshFloor x d := by
  exact ⟨x/d,by simp [meshFloor,mul_comm]⟩

lemma meshFloor_of_dvd (x d : ℤ) (h : d ∣ x) : meshFloor x d=x := by
  exact Int.ediv_mul_cancel h

lemma meshFloor_greatest (x d y : ℤ) (hd : 0 < d) (hy : y ≤ x) (hdy : d ∣ y) :
    y ≤ meshFloor x d := by
  obtain ⟨z,rfl⟩ := hdy
  have hz : z ≤ x/d := (Int.le_ediv_iff_mul_le hd).mpr (by simpa [mul_comm] using hy)
  exact (show d*z ≤ x/d*d by nlinarith)

lemma meshFloor_refinement (x d D : ℤ) (hd : 0 < d) (hD : 0 < D) (hdD : d ∣ D) :
    meshFloor x D ≤ meshFloor x d ∧ meshFloor x d-meshFloor x D < D := by
  have hb := meshFloor_bounds x D hD
  have hb' := meshFloor_bounds x d hd
  exact ⟨meshFloor_greatest x d _ hd hb.1 (dvd_trans hdD (meshFloor_dvd x D)),by omega⟩

theorem meshFloor_refinement_count (x d D : ℤ) (hd : 0 < d) (hD : 0 < D)
    (hdD : d ∣ D) (hratio : D ≤ 16*d) :
    ∃ n : ℕ, n < 16 ∧ meshFloor x D+(n : ℤ)*d=meshFloor x d := by
  have hb := meshFloor_refinement x d D hd hD hdD
  have hdiv : d ∣ meshFloor x d-meshFloor x D :=
    dvd_sub (meshFloor_dvd x d) (dvd_trans hdD (meshFloor_dvd x D))
  obtain ⟨z,hz⟩ := hdiv
  have hz0 : 0 ≤ z := by nlinarith [hb.1]
  have hz16 : z < 16 := by nlinarith [hb.2]
  refine ⟨z.toNat,by omega,?_⟩
  rw [Int.toNat_of_nonneg hz0]
  nlinarith

noncomputable def endpointColumn (x : ℤ) (m j : ℕ) : ℤ := meshFloor x (gridMesh m j)

lemma endpointColumn_last (x : ℤ) (m : ℕ) :
    endpointColumn x m (gridLastLevel m)=x := by
  simp [endpointColumn,gridLastLevel_unit,meshFloor]

lemma endpointColumn_step (x : ℤ) (m j : ℕ) :
    ∃ n : ℕ, n < 16 ∧ endpointColumn x m j+(n : ℤ)*gridMesh m (j+1)=
      endpointColumn x m (j+1) :=
  meshFloor_refinement_count x _ _ (gridMesh_pos m (j+1)) (gridMesh_pos m j)
    (gridMesh_divides m j) (gridMesh_ratio_le m j)

lemma gridMesh_dvd_of_le (m i j : ℕ) (hij : i ≤ j) : gridMesh m j ∣ gridMesh m i := by
  apply pow_dvd_pow
  unfold gridMeshExponent
  omega

lemma endpointColumn_mono (x : ℤ) (m : ℕ) : Monotone (endpointColumn x m) := by
  intro i j hij
  exact meshFloor_greatest x _ _ (gridMesh_pos m j)
    (meshFloor_bounds x _ (gridMesh_pos m i)).1
    (dvd_trans (gridMesh_dvd_of_le m i j hij) (meshFloor_dvd x _))

noncomputable def entranceColumn (x : ℤ) (m J : ℕ) : ℤ :=
  endpointColumn x m J-gridMesh m J
noncomputable def exitColumn (x : ℤ) (m J : ℕ) : ℤ := -entranceColumn (-x) m J

lemma entranceColumn_span (x : ℤ) (m J : ℕ) :
    gridMesh m J ≤ x-entranceColumn x m J ∧
      x-entranceColumn x m J < 2*gridMesh m J := by
  have hb := meshFloor_bounds x (gridMesh m J) (gridMesh_pos m J)
  dsimp [entranceColumn,endpointColumn]
  omega

lemma exitColumn_span (x : ℤ) (m J : ℕ) :
    gridMesh m J ≤ exitColumn x m J-x ∧
      exitColumn x m J-x < 2*gridMesh m J := by
  have hb := entranceColumn_span (-x) m J
  dsimp [exitColumn]
  omega

lemma entranceColumn_dvd (x : ℤ) (m J : ℕ) : gridMesh m J ∣ entranceColumn x m J :=
  dvd_sub (meshFloor_dvd x _) (dvd_refl _)

lemma exitColumn_dvd (x : ℤ) (m J : ℕ) : gridMesh m J ∣ exitColumn x m J :=
  dvd_neg.mpr (entranceColumn_dvd (-x) m J)

end PlanarFPP

end OAI
