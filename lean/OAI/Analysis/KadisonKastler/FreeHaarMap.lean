import OAI.Analysis.KadisonKastler.FreeHaar

namespace OAI

/-! # Transport of free-Haar moments through trace-preserving embeddings -/

namespace KadisonKastler

noncomputable section

variable {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]

theorem starAlgHom_range_map {A : Type*} [CStarAlgebra A]
    (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C) :
    φ.range.map ψ = (ψ.comp φ).range := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨φ a, ⟨a, rfl⟩, rfl⟩

theorem map_haarPower (φ : B →⋆ₐ[ℂ] C) (w : unitary B) (k : ℤ) :
    φ (haarPower w k) =
      haarPower (Unitary.map (StarMonoidHom.ofClass φ) w) k := by
  exact congrArg (fun z : unitary C => (z : C))
    (map_zpow (Unitary.map (StarMonoidHom.ofClass φ)) w k)

/-- Only preservation of the normalized trace is needed to transfer the
alternating moment identities to the image algebra. -/
theorem FreeHaarMoments.map {τ : FaithfulTracialState B} {σ : FaithfulTracialState C}
    {A : StarSubalgebra ℂ B} {w : unitary B} (h : FreeHaarMoments τ A w)
    (φ : B →⋆ₐ[ℂ] C) (hφ : ∀ b, σ.toLinearMap (φ b) = τ.toLinearMap b) :
    FreeHaarMoments σ (A.map φ) (Unitary.map (StarMonoidHom.ofClass φ) w) := by
  constructor
  · intro k hk
    rw [← map_haarPower, hφ]
    exact h.haar_moment k hk
  · intro n hn a k ha ht hk
    choose b hb hba using fun i => StarSubalgebra.mem_map.mp (ha i)
    have hbt : ∀ i, τ.toLinearMap (b i) = 0 := by
      intro i
      rw [← hφ, hba]
      exact ht i
    have he : (List.ofFn (fun i => a i *
        haarPower (Unitary.map (StarMonoidHom.ofClass φ) w) (k i))).prod =
        φ ((List.ofFn (fun i => b i * haarPower w (k i))).prod) := by
      rw [map_list_prod, List.map_ofFn]
      simp only [Function.comp_def, map_mul, map_haarPower, hba]
    rw [he, hφ]
    exact h.alternating_moment n hn b k hb hbt hk

/-- A commuting square of quotient maps transports a unitary lift and its
free moments simultaneously. -/
theorem map_freeHaar_lift {V W : Type*} [CStarAlgebra V] [CStarAlgebra W]
    {τ : FaithfulTracialState B} {σ : FaithfulTracialState C}
    (A : StarSubalgebra ℂ B) (π : V →⋆ₐ[ℂ] B) (α : V →⋆ₐ[ℂ] W)
    (ρ : W →⋆ₐ[ℂ] C) (φ : B →⋆ₐ[ℂ] C)
    (hφ : ∀ b, σ.toLinearMap (φ b) = τ.toLinearMap b)
    (hcomm : ∀ v, φ (π v) = ρ (α v))
    (hv : ∃ v : unitary V, FreeHaarMoments τ A
      (Unitary.map (StarMonoidHom.ofClass π) v)) :
    ∃ v : unitary V, FreeHaarMoments σ (A.map φ)
      (Unitary.map (StarMonoidHom.ofClass ρ)
        (Unitary.map (StarMonoidHom.ofClass α) v)) := by
  obtain ⟨v, hv⟩ := hv
  have h := hv.map φ hφ
  have he : Unitary.map (StarMonoidHom.ofClass φ)
      (Unitary.map (StarMonoidHom.ofClass π) v) =
      Unitary.map (StarMonoidHom.ofClass ρ)
        (Unitary.map (StarMonoidHom.ofClass α) v) := Subtype.ext (hcomm v)
  exact ⟨v, he ▸ h⟩

end

end KadisonKastler

end OAI
