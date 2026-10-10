import OAI.Analysis.Quantum.DimensionTen.PencilKraus
import OAI.Analysis.Quantum.DimensionTen.TensorKraus
import OAI.Analysis.Quantum.DimensionTen.TensorSymmetry

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def exteriorKraus (p : Fin 6 × Fin 6) : Matrix (Fin 6) (Fin 10) ℂ :=
  exteriorIsometryᴴ * (pencilKraus p.1 ⊗ₖ pencilKraus p.2) * symmetricIsometry

lemma exteriorMap_kraus : exteriorMap = krausMap exteriorKraus := by
  funext A
  unfold exteriorMap
  rw [pencilMap_kraus, tensorMap_kraus]
  have h := krausMap_conjugate (fun p : Fin 6 × Fin 6 => pencilKraus p.1 ⊗ₖ pencilKraus p.2)
    symmetricIsometry exteriorIsometryᴴ A
  unfold exteriorKraus
  simpa only [Matrix.conjTranspose_conjTranspose] using h

lemma exteriorMap_output_transpose (A : Mat 10) : (exteriorMap A)ᵀ = exteriorMap A := by
  unfold exteriorMap
  rw [real_compression_transpose _ exteriorIsometry_real]
  rw [tensorMap_output_transpose _ _ pencilMap_output_transpose pencilMap_output_transpose]

lemma exteriorMap_input_transpose (A : Mat 10) : exteriorMap Aᵀ = exteriorMap A := by
  unfold exteriorMap
  rw [← real_embedding_transpose _ symmetricIsometry_real]
  rw [tensorMap_input_transpose _ _ pencilMap_input_transpose pencilMap_input_transpose]

def complementaryKraus (p : Fin 6 × Fin 6) : Matrix (Fin 6) (Fin 10) ℂ :=
  hodgeComplement * exteriorKraus p

lemma complementaryMap_kraus : complementaryMap = krausMap complementaryKraus := by
  funext A
  unfold complementaryMap
  rw [exteriorMap_output_transpose, exteriorMap_kraus, krausMap_postconjugate]
  rfl

lemma complementaryMap_input_transpose (A : Mat 10) : complementaryMap Aᵀ = complementaryMap A := by
  simp only [complementaryMap, exteriorMap_input_transpose]

lemma complementaryMap_output_transpose (A : Mat 10) : (complementaryMap A)ᵀ = complementaryMap A := by
  rw [complementaryMap, real_embedding_transpose _ hodgeComplement_real]
  rw [Matrix.transpose_transpose, exteriorMap_output_transpose]

def phiOneKraus (p : Fin 6 × Fin 6) : Mat 10 := firstSix * exteriorKraus p

def phiTwoKraus (p : Fin 6 × Fin 6) : Mat 10 := (complementaryKraus p)ᴴ * firstSixᴴ

lemma phiOne_kraus : phiOne = krausMap phiOneKraus := by
  funext A
  unfold phiOne
  rw [exteriorMap_input_transpose, exteriorMap_kraus, krausMap_postconjugate]
  rfl

lemma phiTwo_kraus : phiTwo = krausMap phiTwoKraus := by
  funext A
  unfold phiTwo
  rw [complementaryMap_kraus, krausMap_adjoint]
  have h := krausMap_preconjugate (fun k => (complementaryKraus k)ᴴ) firstSixᴴ A
  unfold phiTwoKraus
  simpa only [Matrix.conjTranspose_conjTranspose] using h

lemma phiOne_output_transpose (A : Mat 10) : (phiOne A)ᵀ = phiOne A := by
  unfold phiOne
  rw [real_embedding_transpose _ firstSix_real, exteriorMap_output_transpose]

lemma phiTwo_output_transpose (A : Mat 10) : (phiTwo A)ᵀ = phiTwo A :=
  hsAdjoint_output_transpose _ complementaryMap_input_transpose _

lemma phiOne_ppt : PPT phiOne := by
  refine ⟨?_, ?_, ?_⟩
  · rw [phiOne_kraus]; exact krausMap_linear _
  · rw [phiOne_kraus]; exact krausMap_cp _
  · simp only [phiOne_output_transpose]
    rw [phiOne_kraus]; exact krausMap_cp _

lemma phiTwo_ppt : PPT phiTwo := by
  refine ⟨?_, ?_, ?_⟩
  · rw [phiTwo_kraus]; exact krausMap_linear _
  · rw [phiTwo_kraus]; exact krausMap_cp _
  · simp only [phiTwo_output_transpose]
    rw [phiTwo_kraus]; exact krausMap_cp _

end DimensionTen

end
end

end OAI
