import OAI.Combinatorics.PolynomialVacuum.Bridge.BridgeWordMass

namespace OAI

namespace PolynomialVacuumBridge.Corridor

 

structure ArchWord where
  word : List Bool
  endX : ℤ
  distinct : (traced bottomSource word).Nodup
  terminal : terminalGerm bottomSource word=(.down endX (-1),0)
  inHalfPlane : ∀ v∈traced bottomSource word, 0≤(boxIndex v 0)

namespace ArchWord
@[ext] theorem ext {A B : ArchWord} (h : A.word=B.word) : A=B := by
  have he : A.endX=B.endX := by
    have ht := A.terminal.symm.trans (by rw [h,B.terminal])
    exact Vertex.down.inj (congrArg Prod.fst ht) |>.1
  cases A; cases B; cases h; cases he; rfl

noncomputable def mass (A : ArchWord) : ℝ := criticalActivity^A.word.length
theorem mass_pos (A : ArchWord) : 0 < mass A := pow_pos criticalActivity_pos _

theorem finite_sum_bound (S : Finset ArchWord) :
    (∑ A∈S,mass A) ≤ (Real.cos (3*Real.pi/8))⁻¹ := by
  classical
  let V := S.biUnion (fun A => (traced bottomSource A.word).toFinset)
  let H := V.sup (fun v => (boxIndex v 0).toNat)+1
  have hH : 1≤H := by omega
  have hV : ∀ v∈V,InStrip H v := by
    intro v hv
    obtain ⟨A,hA,ha⟩ := Finset.mem_biUnion.mp hv
    have hnonneg := A.inHalfPlane v (List.mem_toFinset.mp ha)
    have hbound : (boxIndex v 0).toNat<H := Nat.lt_succ_of_le (Finset.le_sup (f := fun v => (boxIndex v 0).toNat) hv)
    simp only [InStrip]
    omega
  obtain ⟨M,hM⟩ := finite_vertices_in_window H V hV
  have hmem : ∀ A∈S,A.word∈sourceExits (vertexWindow H M) bottomSource := by
    intro A hA
    have ht : (terminalGerm bottomSource A.word).1∉vertexWindow H M := by
      intro ht
      have hi := (vertexWindow_strip H M _ ht).1
      rw [A.terminal] at hi
      norm_num [boxIndex] at hi
    apply (mem_sourceExits _ _ _).mpr
    refine ⟨stopped_of_trace _ _ _ A.distinct ?_ ht,ht⟩
    intro v hv
    exact hM (Finset.mem_biUnion.mpr ⟨A,hA,List.mem_toFinset.mpr hv⟩)
  have hi : Set.InjOn ArchWord.word S := fun _ _ _ _ he => ext he
  have he : (∑ A∈S,mass A)=∑ w∈S.image ArchWord.word,criticalActivity^w.length :=
    by simpa only [mass] using (Finset.sum_image (f := fun w : List Bool => criticalActivity^w.length) hi).symm
  rw [he]
  calc
    _ ≤ ∑ w∈sourceExits (vertexWindow H M) bottomSource,criticalActivity^w.length := by
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun w _ _ => (pow_pos criticalActivity_pos _).le)
      intro w hw
      obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hw
      exact hmem A hA
    _ ≤ _ := boundary_source_weight_bound _ bottomSource
      (vertexWindow_convex H M) (bottomSource_mem_window H M hH)
      (bottomSource_outside_of_strip H _ (vertexWindow_strip H M))

theorem mass_summable : Summable (fun A : ArchWord => mass A) := by
  exact summable_of_sum_le (fun A => (mass_pos A).le) finite_sum_bound

theorem mass_le : (∑' A : ArchWord,mass A)≤(Real.cos (3*Real.pi/8))⁻¹ := by
  exact Real.tsum_le_of_sum_le (fun A => (mass_pos A).le) finite_sum_bound

end ArchWord
end PolynomialVacuumBridge.Corridor

end OAI
